# EASY FILE CONVERTER - JUST MODIFY THE SETTINGS BELOW!

param(
    [string]$Preset = "1",  # Change this to "1", "2", "3", or "custom"
    [string]$OutputDir = "C:\Users\Moses\math_ops\OperatorKernelO6\Docs"
)

Write-Host "=== EASY FILE CONVERTER ===" -ForegroundColor Cyan
Write-Host "Preset: $Preset" -ForegroundColor Green
Write-Host ""

# ===== EASY CONFIGURATION - MODIFY THESE LISTS =====

$PRESET_1_FILES = @(
    "C:\Users\Moses\math_ops\OperatorKernelO6\Core_Docs\Operator Centric Foundations of Godelian Incompleteness.md",
    "C:\Users\Moses\math_ops\OperatorKernelO6\Core_Docs\Termination_Companion.md"
)

$PRESET_2_FILES = @(
    "C:\Users\Moses\math_ops\OperatorKernelO6\OperatorKernelO6\Meta\Godel.lean",
    "C:\Users\Moses\math_ops\OperatorKernelO6\OperatorKernelO6\Meta\Normalize.lean"
)

$PRESET_3_FILES = @(
    "C:\Users\Moses\math_ops\OperatorKernelO6\Core_Docs\Operator Centric Foundations of Godelian Incompleteness.md",
    "C:\Users\Moses\math_ops\OperatorKernelO6\OperatorKernelO6\Meta\Godel.lean"
)

# For custom preset, add your files here:
$CUSTOM_FILES = @(
    "C:\Users\Moses\math_ops\OperatorKernelO6\OperatorKernelO6\Kernel.lean"
    # Add more files here as needed
)

# ===== END CONFIGURATION =====

# Select files based on preset
$filesToProcess = @()
$title = ""

switch ($Preset) {
    "1" { 
        $filesToProcess = $PRESET_1_FILES
        $title = "Core_Theory_Docs"
        Write-Host "Using Preset 1: Core Theory Documents" -ForegroundColor Yellow
    }
    "2" { 
        $filesToProcess = $PRESET_2_FILES 
        $title = "Meta_Lean_Files"
        Write-Host "Using Preset 2: Meta Lean Files" -ForegroundColor Yellow
    }
    "3" { 
        $filesToProcess = $PRESET_3_FILES
        $title = "Core_And_Godel" 
        Write-Host "Using Preset 3: Core + Godel" -ForegroundColor Yellow
    }
    "custom" { 
        $filesToProcess = $CUSTOM_FILES
        $title = "Custom_Selection"
        Write-Host "Using Custom Files" -ForegroundColor Yellow
    }
    default { 
        Write-Host "Invalid preset! Use 1, 2, 3, or custom" -ForegroundColor Red
        exit 
    }
}

Write-Host ""
Write-Host "Files to process:" -ForegroundColor Cyan
$validFiles = @()
foreach ($file in $filesToProcess) {
    if (Test-Path $file) {
        $fileName = [System.IO.Path]::GetFileName($file)
        Write-Host "  ✓ $fileName" -ForegroundColor Green
        $validFiles += $file
    } else {
        $fileName = [System.IO.Path]::GetFileName($file)  
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

# HTML generation function
function Create-HTML {
    param([string]$Title, [string]$Content, [string]$FilePath)
    
    $fileType = if ($FilePath -like "*.md") { "markdown" } else { "lean" }
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    
    # Convert content based on type
    if ($fileType -eq "markdown") {
        $htmlContent = $Content
        $htmlContent = $htmlContent -replace '(?m)^### (.*)', '<h3>$1</h3>'
        $htmlContent = $htmlContent -replace '(?m)^## (.*)', '<h2>$1</h2>'
        $htmlContent = $htmlContent -replace '(?m)^# (.*)', '<h1>$1</h1>'
        $htmlContent = $htmlContent -replace '\*\*(.*?)\*\*', '<strong>$1</strong>'
        $htmlContent = $htmlContent -replace '\*(.*?)\*', '<em>$1</em>'
        $htmlContent = $htmlContent -replace '`([^`]+)`', '<code>$1</code>'
        $htmlContent = $htmlContent -replace '(?m)\n\n', '</p><p>'
        $htmlContent = "<div class='content'><p>$htmlContent</p></div>"
    } else {
        $htmlContent = "<pre><code class='lean'>" + [System.Web.HttpUtility]::HtmlEncode($Content) + "</code></pre>"
    }

    return @"
<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>$Title</title>
    <style>
        body { 
            max-width: 1000px; 
            margin: 0 auto; 
            padding: 20px; 
            font-family: -apple-system, system-ui, sans-serif;
            line-height: 1.6;
        }
        h1 { 
            color: #2c3e50; 
            border-bottom: 3px solid #3498db; 
            padding-bottom: 10px; 
            margin-bottom: 20px;
        }
        h2 { color: #34495e; margin-top: 30px; }
        h3 { color: #2c3e50; }
        pre { 
            background: #f8f9fa; 
            padding: 15px; 
            border-radius: 5px; 
            overflow-x: auto; 
            border: 1px solid #dee2e6;
            font-family: 'Consolas', 'Monaco', monospace;
            font-size: 14px;
        }
        code { 
            font-family: 'Consolas', 'Monaco', monospace; 
            background: #f1f2f6;
            padding: 2px 4px;
            border-radius: 3px;
        }
        .meta { 
            background: #e8f4fd; 
            padding: 15px; 
            border-radius: 5px; 
            margin: 20px 0;
            color: #2c3e50;
        }
        .content p { margin-bottom: 15px; }
    </style>
</head>
<body>
    <h1>$Title</h1>
    <div class="meta">
        <strong>File:</strong> $FilePath<br>
        <strong>Type:</strong> $fileType<br>
        <strong>Generated:</strong> $timestamp
    </div>
    $htmlContent
</body>
</html>
"@
}

# Process each file
$processedFiles = @()
foreach ($filePath in $validFiles) {
    $fileName = [System.IO.Path]::GetFileNameWithoutExtension($filePath)
    $safeName = $fileName -replace '[^\w\-_]', '_'
    
    Write-Host "Processing: $fileName" -ForegroundColor Cyan
    
    # Read file content
    $content = Get-Content $filePath -Raw -Encoding UTF8
    if ([string]::IsNullOrWhiteSpace($content)) {
        $content = "-- File appears to be empty --"
    }
    
    # Generate HTML
    $html = Create-HTML -Title $fileName -Content $content -FilePath $filePath
    $htmlOutputPath = Join-Path $OutputDir "$safeName.html"
    $html | Out-File -FilePath $htmlOutputPath -Encoding UTF8
    
    Write-Host "  ✓ Created: $safeName.html" -ForegroundColor Green
    
    $processedFiles += @{
        Name = $fileName
        Content = $content
        Path = $filePath
        Type = if ($filePath -like "*.md") { "markdown" } else { "lean" }
    }
}

# Create combined document
if ($processedFiles.Count -gt 1) {
    Write-Host ""
    Write-Host "Creating combined document..." -ForegroundColor Cyan
    
    $combinedContent = "# $title`n`nCombined document containing $($processedFiles.Count) files.`n`n"
    $combinedContent += "## Table of Contents`n`n"
    
    # Add table of contents
    foreach ($file in $processedFiles) {
        $combinedContent += "- [$($file.Name)]($($file.Path))`n"
    }
    $combinedContent += "`n---`n"
    
    # Add each file's content
    foreach ($file in $processedFiles) {
        $combinedContent += "`n## $($file.Name)`n`n"
        $combinedContent += "**Source:** ``$($file.Path)```n`n"
        $combinedContent += "``````$($file.Type)`n"
        $combinedContent += $file.Content
        $combinedContent += "`n``````"
        $combinedContent += "`n`n---`n"
    }
    
    $combinedHtml = Create-HTML -Title "$title Combined" -Content $combinedContent -FilePath "Combined Document"
    $combinedOutputPath = Join-Path $OutputDir "$title`_Combined.html"
    $combinedHtml | Out-File -FilePath $combinedOutputPath -Encoding UTF8
    
    Write-Host "  ✓ Created: $title`_Combined.html" -ForegroundColor Green
}

Write-Host ""
Write-Host "CONVERSION COMPLETE!" -ForegroundColor Green
Write-Host "Output directory: $OutputDir" -ForegroundColor White
Write-Host "Individual files: $($processedFiles.Count)" -ForegroundColor Gray
if ($processedFiles.Count -gt 1) {
    Write-Host "Combined document: $title`_Combined.html" -ForegroundColor Gray
}

Write-Host ""
Write-Host "USAGE EXAMPLES:" -ForegroundColor Yellow
Write-Host "  .\easy_converter.ps1                    # Uses preset 1" -ForegroundColor White
Write-Host "  .\easy_converter.ps1 -Preset 2          # Uses preset 2" -ForegroundColor White  
Write-Host "  .\easy_converter.ps1 -Preset custom     # Uses custom files" -ForegroundColor White
Write-Host ""
Write-Host "To customize: Edit the file lists at the top of this script!" -ForegroundColor Cyan