param([string]$OutputDir = "C:\Users\Moses\math_ops\OperatorKernelO6\Docs")

Write-Host "BASIC FILE CONVERTER" -ForegroundColor Cyan

# EDIT THESE PATHS TO CONVERT YOUR FILES:
$files = @(
    "C:\Users\Moses\math_ops\OperatorKernelO6\Core_Docs\Operator Centric Foundations of Godelian Incompleteness.md",
    "C:\Users\Moses\math_ops\OperatorKernelO6\Core_Docs\Termination_Companion.md"
)

$title = "Core_Theory_Documents"

Write-Host "Processing files..." -ForegroundColor Green

New-Item -ItemType Directory -Path $OutputDir -Force | Out-Null
Add-Type -AssemblyName System.Web

$processed = @()

foreach ($file in $files) {
    if (Test-Path $file) {
        $name = [System.IO.Path]::GetFileNameWithoutExtension($file)
        $content = Get-Content $file -Raw -Encoding UTF8
        
        Write-Host "Processing: $name" -ForegroundColor White
        
        $html = @"
<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<title>$name</title>
<style>
body { max-width: 800px; margin: 0 auto; padding: 20px; font-family: Arial; }
h1 { color: #2c3e50; }
pre { background: #f5f5f5; padding: 15px; }
</style>
</head>
<body>
<h1>$name</h1>
<pre>$([System.Web.HttpUtility]::HtmlEncode($content))</pre>
</body>
</html>
"@
        
        $safeName = $name -replace '[^\w\-]', '_'
        $outputPath = Join-Path $OutputDir "$safeName.html"
        $html | Out-File -FilePath $outputPath -Encoding UTF8
        
        Write-Host "Created: $safeName.html" -ForegroundColor Green
        
        $processed += @{Name = $name; Content = $content}
    }
}

Write-Host ""
Write-Host "DONE! Files saved to: $OutputDir" -ForegroundColor Green
Write-Host "Processed: $($processed.Count) files" -ForegroundColor White