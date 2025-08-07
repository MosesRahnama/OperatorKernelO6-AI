$files = @(
    'C:\Users\Moses\math_ops\OperatorKernelO6\core_docs\ko6_guide.md',
    'C:\Users\Moses\math_ops\OperatorKernelO6\OperatorKernelO6\Meta\Termination.lean'
)
$title = 'Full_Test'
$outputDir = 'C:\Users\Moses\math_ops\OperatorKernelO6\TestDocs'

Write-Host "FULL END-TO-END TEST" -ForegroundColor Cyan
Write-Host "Processing files..." -ForegroundColor Green

New-Item -ItemType Directory -Path $outputDir -Force | Out-Null
Add-Type -AssemblyName System.Web

$processed = @()
foreach ($file in $files) {
    if (Test-Path $file) {
        $name = [System.IO.Path]::GetFileNameWithoutExtension($file)
        Write-Host "Processing: $name" -ForegroundColor White
        
        $content = Get-Content $file -Raw -Encoding UTF8
        $isMarkdown = $file -like "*.md"
        
        # Create HTML content with FIXED markdown conversion
        $htmlContent = if ($isMarkdown) {
            $html = $content
            $html = $html -replace '(?m)^### (.*)', '<h3>$1</h3>'
            $html = $html -replace '(?m)^## (.*)', '<h2>$1</h2>'  
            $html = $html -replace '(?m)^# (.*)', '<h1>$1</h1>'
            $html = $html -replace '\*\*([^*]+)\*\*', '<strong>$1</strong>'
            $html = $html -replace '\*([^*]+)\*', '<em>$1</em>'
            $html = $html -replace '`([^`]+)`', '<code>$1</code>'
            $paragraphs = $html -split "`n`n" | Where-Object { $_.Trim() -ne "" }
            $htmlParagraphs = $paragraphs | ForEach-Object { "<p>$($_.Trim())</p>" }
            $htmlParagraphs -join "`n"
        } else {
            "<pre class='lean-code'>" + [System.Web.HttpUtility]::HtmlEncode($content) + "</pre>"
        }
        
        $docType = if ($isMarkdown) { "Markdown Document" } else { "Lean Proof Code" }
        $timestamp = Get-Date -Format 'MMMM d, yyyy \a\t h:mm tt'
        
        $html = @"
<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<title>$name</title>
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
.header { 
    text-align: center; 
    margin-bottom: 40px; 
    border-bottom: 2px solid #000; 
    padding-bottom: 20px; 
}
.title { 
    font-size: 18pt; 
    font-weight: bold; 
    margin-bottom: 10px; 
    text-transform: uppercase; 
    letter-spacing: 1px; 
}
.author { 
    font-size: 14pt; 
    font-style: italic; 
    margin-bottom: 5px; 
}
.affiliation { 
    font-size: 11pt; 
    color: #666; 
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
.lean-code { 
    background: #f9f9f9; 
    padding: 15pt; 
    border: 1px solid #ddd; 
    font-family: 'Courier New', Courier, monospace; 
    font-size: 10pt; 
    line-height: 1.4; 
    overflow-x: auto; 
    white-space: pre-wrap; 
    margin: 15pt 0; 
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
em { 
    font-style: italic; 
}
.file-info { 
    background: #f0f0f0; 
    border: 1px solid #ccc; 
    padding: 10pt; 
    margin: 20pt 0; 
    font-size: 10pt; 
    color: #666; 
}
</style>
</head>
<body>
    <div class="header">
        <div class="title">$name</div>
        <div class="author">Moses Rahnama</div>
        <div class="affiliation">Mina Analytics</div>
    </div>
    <div class="file-info">
        <strong>Source:</strong> $file<br>
        <strong>Type:</strong> $docType<br>
        <strong>Generated:</strong> $timestamp
    </div>
    $htmlContent
</body>
</html>
"@
        
        $safeName = $name -replace '[^\w\-]', '_'
        $outputPath = Join-Path $outputDir "$safeName.html"
        $html | Out-File -FilePath $outputPath -Encoding UTF8
        Write-Host "  ✓ $safeName.html" -ForegroundColor Green
        
        $processed += @{ Name = $name; Content = $content; Type = if ($isMarkdown) { "markdown" } else { "lean" }; Path = $file }
    }
}

Write-Host ""
Write-Host "CONVERSION COMPLETE!" -ForegroundColor Green
Write-Host "Files processed: $($processed.Count)" -ForegroundColor Gray
Write-Host "Output: $outputDir" -ForegroundColor White
Write-Host ""
Write-Host "Font sizes are controlled (no 300pt issues)" -ForegroundColor Green
Write-Host "Academic styling with Times New Roman" -ForegroundColor Green
Write-Host "Moses Rahnama Mina Analytics byline" -ForegroundColor Green