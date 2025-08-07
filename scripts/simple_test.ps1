Write-Host "TESTING CONVERSION..." -ForegroundColor Cyan

$files = @(
    'C:\Users\Moses\math_ops\OperatorKernelO6\core_docs\ko6_guide.md'
)
$outputDir = 'C:\Users\Moses\math_ops\OperatorKernelO6\TestDocs'

New-Item -ItemType Directory -Path $outputDir -Force | Out-Null
Add-Type -AssemblyName System.Web

foreach ($file in $files) {
    if (Test-Path $file) {
        $name = [System.IO.Path]::GetFileNameWithoutExtension($file)
        $content = Get-Content $file -Raw -Encoding UTF8
        $isMarkdown = $file -like "*.md"
        
        Write-Host "Processing: $name" -ForegroundColor White
        
        $htmlContent = if ($isMarkdown) {
            $html = $content
            $html = $html -replace '(?m)^# (.*)', '<h1>$1</h1>'
            $html = $html -replace '(?m)^## (.*)', '<h2>$1</h2>'  
            $html = $html -replace '(?m)^### (.*)', '<h3>$1</h3>'
            $paragraphs = $html -split "`n`n" | Where-Object { $_.Trim() -ne "" }
            $htmlParagraphs = $paragraphs | ForEach-Object { "<p>$($_.Trim())</p>" }
            $htmlParagraphs -join "`n"
        } else {
            "<pre>" + [System.Web.HttpUtility]::HtmlEncode($content) + "</pre>"
        }
        
        $html = @"
<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<title>$name</title>
<style>
body { font-family: 'Times New Roman', serif; font-size: 12pt; max-width: 800px; margin: 0 auto; padding: 30px; }
h1 { font-size: 16pt; text-align: center; margin-bottom: 20px; }
h2 { font-size: 14pt; margin-top: 25px; }
h3 { font-size: 12pt; margin-top: 20px; }
p { font-size: 12pt; text-align: justify; margin-bottom: 12pt; }
</style>
</head>
<body>
<h1>$name - Moses Rahnama, Mina Analytics</h1>
$htmlContent
</body>
</html>
"@
        
        $outputPath = Join-Path $outputDir "$name`_simple.html"
        $html | Out-File -FilePath $outputPath -Encoding UTF8
        Write-Host "Created: $name`_simple.html" -ForegroundColor Green
    }
}

Write-Host "Test complete!" -ForegroundColor Green