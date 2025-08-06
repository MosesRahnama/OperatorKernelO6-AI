# BASIC FILE CONVERTER - JUST WORKS!
param([string]$OutputDir = "C:\Users\Moses\math_ops\OperatorKernelO6\Docs")

Write-Host "=== BASIC FILE CONVERTER ===" -ForegroundColor Cyan

# CONFIGURE YOUR FILES HERE - SUPER EASY!
$FILES_TO_CONVERT = @(
    "C:\Users\Moses\math_ops\OperatorKernelO6\Core_Docs\Operator Centric Foundations of Godelian Incompleteness.md",
    "C:\Users\Moses\math_ops\OperatorKernelO6\Core_Docs\Termination_Companion.md"
    # Add more files here - just copy/paste the full path!
)

$TITLE = "Core_Theory_Documents"  # Change this to whatever you want

Write-Host "Converting $($FILES_TO_CONVERT.Count) files..." -ForegroundColor Green
Write-Host ""

# Create output directory
New-Item -ItemType Directory -Path $OutputDir -Force | Out-Null
Add-Type -AssemblyName System.Web

$processedFiles = @()
$fileIndex = 1

foreach ($filePath in $FILES_TO_CONVERT) {
    if (Test-Path $filePath) {
        $fileName = [System.IO.Path]::GetFileNameWithoutExtension($filePath)
        Write-Host "[$fileIndex/$($FILES_TO_CONVERT.Count)] Processing: $fileName" -ForegroundColor White
        
        # Read content
        $content = Get-Content $filePath -Raw -Encoding UTF8
        if (!$content) { $content = "-- Empty file --" }
        
        # Determine type
        $isMarkdown = $filePath -like "*.md"
        
        # Create simple HTML
        $htmlContent = if ($isMarkdown) {
            $html = $content
            $html = $html -replace '## ', '<h2>'
            $html = $html -replace '# ', '<h1>'  
            $html = $html -replace '\*\*([^*]+)\*\*', '<strong>$1</strong>'
            "<div>$html</div>"
        } else {
            "<pre>" + [System.Web.HttpUtility]::HtmlEncode($content) + "</pre>"
        }
        
        # Simple HTML template
        $html = @"
<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<title>$fileName</title>
<style>
body { max-width: 800px; margin: 0 auto; padding: 20px; font-family: Arial, sans-serif; }
h1 { color: #2c3e50; }
h2 { color: #34495e; }
pre { background: #f5f5f5; padding: 15px; }
</style>
</head>
<body>
<h1>$fileName</h1>
$htmlContent
</body>
</html>
"@
        
        # Save individual file
        $safeFileName = $fileName -replace '[^\w\-]', '_'
        $outputPath = Join-Path $OutputDir "$safeFileName.html"
        $html | Out-File -FilePath $outputPath -Encoding UTF8
        Write-Host "  Created: $safeFileName.html" -ForegroundColor Green
        
        # Store for combined document
        $processedFiles += @{
            Name = $fileName
            Content = $content
            Type = if ($isMarkdown) { "markdown" } else { "lean" }
        }
        
        $fileIndex++
    } else {
        Write-Host "File not found: $([System.IO.Path]::GetFileName($filePath))" -ForegroundColor Red
    }
}

# Create combined document
if ($processedFiles.Count -gt 1) {
    Write-Host ""
    Write-Host "Creating combined document..." -ForegroundColor Cyan
    
    $combinedContent = "# $TITLE`n`n"
    $combinedContent += "This document contains $($processedFiles.Count) files:`n`n"
    
    foreach ($file in $processedFiles) {
        $combinedContent += "## $($file.Name)`n`n"
        $combinedContent += "```$($file.Type)`n"
        $combinedContent += $file.Content
        $combinedContent += "`n```"
        $combinedContent += "`n`n---`n`n"
    }
    
    # Convert combined content to HTML
    $combinedHtml = $combinedContent
    $combinedHtml = $combinedHtml -replace '## ([^`r`n]+)', '<h2>$1</h2>'
    $combinedHtml = $combinedHtml -replace '# ([^`r`n]+)', '<h1>$1</h1>'
    $combinedHtml = $combinedHtml -replace '```[^`r`n]*`n([^`]+)```', '<pre>$1</pre>'
    
    $combinedHtmlDoc = @"
<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<title>$TITLE</title>
<style>
body { max-width: 800px; margin: 0 auto; padding: 20px; font-family: Arial, sans-serif; }
h1 { color: #2c3e50; border-bottom: 2px solid #3498db; padding-bottom: 10px; }
h2 { color: #34495e; margin-top: 30px; }
pre { background: #f5f5f5; padding: 15px; border-radius: 5px; overflow-x: auto; }
</style>
</head>
<body>
$combinedHtml
</body>
</html>
"@
    
    $combinedPath = Join-Path $OutputDir "$TITLE.html"
    $combinedHtmlDoc | Out-File -FilePath $combinedPath -Encoding UTF8
    Write-Host "  Created: $TITLE.html" -ForegroundColor Green
}

Write-Host ""
Write-Host "CONVERSION COMPLETE!" -ForegroundColor Green
Write-Host "Files saved to: $OutputDir" -ForegroundColor White
Write-Host ""
Write-Host "TO CUSTOMIZE:" -ForegroundColor Yellow
Write-Host "1. Edit the FILES_TO_CONVERT array (lines 6-10)" -ForegroundColor Gray
Write-Host "2. Change the TITLE variable (line 12)" -ForegroundColor Gray
Write-Host "3. Run the script again!" -ForegroundColor Gray