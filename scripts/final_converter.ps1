param([string]$OutputDir = "C:\Users\Moses\math_ops\OperatorKernelO6\Docs")

Write-Host "FLEXIBLE FILE CONVERTER" -ForegroundColor Cyan
Write-Host "Total control over your file selection and ordering!" -ForegroundColor Green
Write-Host ""

# ===== EASY CONFIGURATION SECTION =====
# Just modify these arrays to pick exactly what you want!

# Preset 1: Core theory documents
$PRESET_1 = @(
    "C:\Users\Moses\math_ops\OperatorKernelO6\Core_Docs\Operator Centric Foundations of Godelian Incompleteness.md",
    "C:\Users\Moses\math_ops\OperatorKernelO6\Core_Docs\Termination_Companion.md"
)

# Preset 2: Meta lean files
$PRESET_2 = @(
    "C:\Users\Moses\math_ops\OperatorKernelO6\OperatorKernelO6\Meta\Godel.lean",
    "C:\Users\Moses\math_ops\OperatorKernelO6\OperatorKernelO6\Meta\Normalize.lean"
)

# Preset 3: Mixed content in custom order
$PRESET_3 = @(
    "C:\Users\Moses\math_ops\OperatorKernelO6\OperatorKernelO6\Meta\Godel.lean",
    "C:\Users\Moses\math_ops\OperatorKernelO6\Core_Docs\Operator Centric Foundations of Godelian Incompleteness.md",
    "C:\Users\Moses\math_ops\OperatorKernelO6\Core_Docs\Termination_Companion.md"
)

# Custom selection - add any files you want here:
$CUSTOM = @(
    # "C:\Users\Moses\math_ops\OperatorKernelO6\OperatorKernelO6\Kernel.lean",
    # "C:\Users\Moses\math_ops\OperatorKernelO6\Core_Docs\ordinal-toolkit.md"
    # Add your files here...
)

# ===== END CONFIGURATION =====

# Ask user which preset to use
Write-Host "Available presets:" -ForegroundColor Yellow
Write-Host "  [1] Core Theory (Foundations + Termination)" -ForegroundColor White
Write-Host "  [2] Meta Lean Files (Godel + Normalize)" -ForegroundColor White
Write-Host "  [3] Mixed Content (Godel + Both Core Docs)" -ForegroundColor White
Write-Host "  [4] Custom Selection (edit CUSTOM array above)" -ForegroundColor White
Write-Host ""

$choice = Read-Host "Choose preset (1-4) or press Enter for preset 1"
if (!$choice) { $choice = "1" }

# Select files based on choice
$files = @()
$title = ""

switch ($choice) {
    "1" { $files = $PRESET_1; $title = "Core_Theory" }
    "2" { $files = $PRESET_2; $title = "Meta_Lean" }
    "3" { $files = $PRESET_3; $title = "Mixed_Content" }
    "4" { $files = $CUSTOM; $title = "Custom_Selection" }
    default { $files = $PRESET_1; $title = "Core_Theory" }
}

Write-Host ""
Write-Host "Selected: $title" -ForegroundColor Green
Write-Host "Files to process:" -ForegroundColor Cyan

$validFiles = @()
foreach ($file in $files) {
    $fileName = [System.IO.Path]::GetFileName($file)
    if (Test-Path $file) {
        Write-Host "  ✓ $fileName" -ForegroundColor Green
        $validFiles += $file
    } else {
        Write-Host "  ✗ $fileName (not found)" -ForegroundColor Red
    }
}

if ($validFiles.Count -eq 0) {
    Write-Host ""
    Write-Host "No valid files found! Check your file paths." -ForegroundColor Red
    exit
}

Write-Host ""
Write-Host "Processing $($validFiles.Count) files..." -ForegroundColor White

# Create output directory
New-Item -ItemType Directory -Path $OutputDir -Force | Out-Null
Add-Type -AssemblyName System.Web

# Process each file
$processed = @()
$index = 1

foreach ($file in $validFiles) {
    $name = [System.IO.Path]::GetFileNameWithoutExtension($file)
    $isMarkdown = $file -like "*.md"
    
    Write-Host "[$index/$($validFiles.Count)] $name" -ForegroundColor White
    
    # Read content
    $content = Get-Content $file -Raw -Encoding UTF8
    if (!$content) { $content = "-- File appears to be empty --" }
    
    # Create HTML with proper formatting
    $htmlContent = if ($isMarkdown) {
        # Basic markdown to HTML conversion
        $html = $content
        $html = $html -replace '(?m)^### (.*)', '<h3>$1</h3>'
        $html = $html -replace '(?m)^## (.*)', '<h2>$1</h2>'
        $html = $html -replace '(?m)^# (.*)', '<h1 class="doc-header">$1</h1>'
        $html = $html -replace '\*\*([^*]+)\*\*', '<strong>$1</strong>'
        $html = $html -replace '\*([^*]+)\*', '<em>$1</em>'
        $html = $html -replace '`([^`]+)`', '<code>$1</code>'
        "<div class='markdown'>$html</div>"
    } else {
        "<pre class='lean-code'>" + [System.Web.HttpUtility]::HtmlEncode($content) + "</pre>"
    }
    
    # Enhanced HTML template
    $html = @"
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>$name</title>
    <style>
        body { 
            max-width: 1000px; 
            margin: 0 auto; 
            padding: 30px; 
            font-family: system-ui, -apple-system, sans-serif;
            line-height: 1.6;
            color: #333;
        }
        h1 { 
            color: #2c3e50; 
            border-bottom: 3px solid #3498db; 
            padding-bottom: 10px;
            margin-bottom: 25px;
        }
        .doc-header {
            color: #2c3e50;
            font-size: 1.8em;
            margin-top: 30px;
            margin-bottom: 15px;
        }
        h2 { color: #34495e; margin-top: 25px; }
        h3 { color: #2c3e50; margin-top: 20px; }
        .lean-code { 
            background: #f8f9fa; 
            padding: 20px; 
            border-radius: 8px;
            border: 1px solid #dee2e6;
            font-family: 'Consolas', 'Monaco', monospace;
            font-size: 14px;
            overflow-x: auto;
            white-space: pre-wrap;
        }
        .markdown { line-height: 1.7; }
        code { 
            background: #f1f2f6;
            padding: 2px 6px;
            border-radius: 3px;
            font-family: 'Consolas', monospace;
            font-size: 0.9em;
        }
        .file-info {
            background: #e8f4fd;
            padding: 15px;
            border-radius: 8px;
            margin-bottom: 25px;
            font-size: 0.9em;
        }
    </style>
</head>
<body>
    <h1>$name</h1>
    <div class="file-info">
        <strong>File:</strong> $file<br>
        <strong>Type:</strong> $(if ($isMarkdown) { 'Markdown' } else { 'Lean' })<br>
        <strong>Generated:</strong> $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')
    </div>
    $htmlContent
</body>
</html>
"@
    
    # Save individual file
    $safeName = $name -replace '[^\w\-]', '_'
    $outputPath = Join-Path $OutputDir "$safeName.html"
    $html | Out-File -FilePath $outputPath -Encoding UTF8
    Write-Host "    ✓ $safeName.html" -ForegroundColor Green
    
    $processed += @{
        Name = $name
        Content = $content
        Type = if ($isMarkdown) { "markdown" } else { "lean" }
        Path = $file
    }
    
    $index++
}

# Create combined document
if ($processed.Count -gt 1) {
    Write-Host ""
    Write-Host "Creating combined document..." -ForegroundColor Cyan
    
    # Build combined content
    $combinedContent = "# $title Combined`n`n"
    $combinedContent += "This document contains $($processed.Count) files in the specified order:`n`n"
    
    # Table of contents
    $combinedContent += "## Table of Contents`n`n"
    foreach ($file in $processed) {
        $combinedContent += "- [$($file.Name)]($($file.Path))`n"
    }
    $combinedContent += "`n---`n`n"
    
    # Add each file's content
    foreach ($file in $processed) {
        $combinedContent += "## $($file.Name)`n`n"
        $combinedContent += "**Source:** $($file.Path)`n`n"
        $combinedContent += "``````$($file.Type)`n"
        $combinedContent += $file.Content
        $combinedContent += "`n```"
        $combinedContent += "`n`n---`n`n"
    }
    
    # Convert to HTML (basic)
    $combinedHtml = $combinedContent
    $combinedHtml = $combinedHtml -replace '(?m)^## ([^`r`n]+)', '<h2>$1</h2>'
    $combinedHtml = $combinedHtml -replace '(?m)^# ([^`r`n]+)', '<h1>$1</h1>'
    $combinedHtml = $combinedHtml -replace '```[^`r`n]*`r?`n([^`]+?)```', '<pre>$1</pre>'
    $combinedHtml = $combinedHtml -replace '\*\*([^*]+)\*\*', '<strong>$1</strong>'
    $combinedHtml = $combinedHtml -replace '(?m)^- (.+)', '<li>$1</li>'
    
    $combinedDoc = @"
<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<title>$title Combined</title>
<style>
body { max-width: 1000px; margin: 0 auto; padding: 30px; font-family: system-ui; line-height: 1.6; }
h1 { color: #2c3e50; border-bottom: 3px solid #3498db; padding-bottom: 10px; }
h2 { color: #34495e; margin-top: 30px; }
pre { background: #f8f9fa; padding: 20px; border-radius: 8px; overflow-x: auto; }
li { margin-bottom: 5px; }
</style>
</head>
<body>
$combinedHtml
</body>
</html>
"@
    
    $combinedPath = Join-Path $OutputDir "$title`_Combined.html"
    $combinedDoc | Out-File -FilePath $combinedPath -Encoding UTF8
    Write-Host "    ✓ $title`_Combined.html" -ForegroundColor Green
}

Write-Host ""
Write-Host "CONVERSION COMPLETE!" -ForegroundColor Green
Write-Host "Output directory: $OutputDir" -ForegroundColor White
Write-Host "Files processed: $($processed.Count)" -ForegroundColor Gray
if ($processed.Count -gt 1) {
    Write-Host "Combined document: Yes" -ForegroundColor Gray
}

Write-Host ""
Write-Host "HOW TO CUSTOMIZE:" -ForegroundColor Yellow
Write-Host "1. Edit the PRESET arrays at the top of this script" -ForegroundColor White
Write-Host "2. Add/remove/reorder files as needed" -ForegroundColor White
Write-Host "3. Run the script again!" -ForegroundColor White