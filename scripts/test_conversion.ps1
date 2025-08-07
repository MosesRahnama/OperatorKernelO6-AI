$file = 'C:\Users\Moses\math_ops\OperatorKernelO6\core_docs\ko6_guide.md'
$outputDir = 'C:\Users\Moses\math_ops\OperatorKernelO6\TestDocs'

Write-Host "Testing markdown conversion..." -ForegroundColor Cyan
New-Item -ItemType Directory -Path $outputDir -Force | Out-Null
Add-Type -AssemblyName System.Web

$content = Get-Content $file -Raw -Encoding UTF8
Write-Host "Content length: $($content.Length) chars"

# Test markdown conversion with FIXED font handling
$html = $content
$html = $html -replace '(?m)^### (.*)', '<h3>$1</h3>'
$html = $html -replace '(?m)^## (.*)', '<h2>$1</h2>'  
$html = $html -replace '(?m)^# (.*)', '<h1>$1</h1>'
$html = $html -replace '\*\*([^*]+)\*\*', '<strong>$1</strong>'
$html = $html -replace '\*([^*]+)\*', '<em>$1</em>'
$html = $html -replace '`([^`]+)`', '<code>$1</code>'

# Convert paragraphs properly
$paragraphs = $html -split "`n`n" | Where-Object { $_.Trim() -ne "" }
$htmlParagraphs = $paragraphs | ForEach-Object { "<p>$($_.Trim())</p>" }
$htmlContent = $htmlParagraphs -join "`n"

$fullHtml = @"
<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<title>Test MD Conversion</title>
<style>
body { 
    max-width: 800px; 
    margin: 0 auto; 
    padding: 40px 30px; 
    font-family: 'Times New Roman', Times, serif; 
    font-size: 12pt; 
    line-height: 1.6;
    color: #000; 
    background: #fff;
}
h1 { 
    font-size: 16pt; 
    font-weight: bold; 
    color: #000; 
    margin-top: 30px; 
    margin-bottom: 15px; 
    text-align: center; 
}
h2 { 
    font-size: 14pt; 
    font-weight: bold; 
    color: #000; 
    margin-top: 25px; 
    margin-bottom: 12px; 
    border-bottom: 1px solid #ccc; 
    padding-bottom: 5px; 
}
h3 { 
    font-size: 12pt; 
    font-weight: bold; 
    color: #000; 
    margin-top: 20px; 
    margin-bottom: 10px; 
}
p { 
    font-size: 12pt;
    text-align: justify; 
    margin-bottom: 12pt; 
    text-indent: 0.5in; 
}
code { 
    background: #f5f5f5; 
    padding: 2pt 4pt; 
    border: 1px solid #ddd; 
    font-family: 'Courier New', monospace; 
    font-size: 10pt; 
}
strong { 
    font-weight: bold; 
}
</style>
</head>
<body>
$htmlContent
</body>
</html>
"@

$outputPath = Join-Path $outputDir "test_md_conversion.html"
$fullHtml | Out-File -FilePath $outputPath -Encoding UTF8
Write-Host "Created: $outputPath" -ForegroundColor Green

# Check the HTML content for font size issues
$lines = $fullHtml -split "`n"
$fontSizeLines = $lines | Where-Object { $_ -match "font-size" }
Write-Host "`nFont size specifications found:" -ForegroundColor Yellow
$fontSizeLines | ForEach-Object { Write-Host "  $_" }

Write-Host "`nFirst 200 chars of HTML content:" -ForegroundColor White
Write-Host $htmlContent.Substring(0, [Math]::Min(200, $htmlContent.Length))

Write-Host "`nConversion test complete!" -ForegroundColor Green