param(
    [string]$OutputDir = "C:\Users\Moses\math_ops\OperatorKernelO6\Docs",
    [switch]$QuickMode
)

Write-Host "=== FLEXIBLE FILE CONVERTER - TOTAL CONTROL! ===" -ForegroundColor Cyan
Write-Host "Select ANY files from ANY directory in ANY order!" -ForegroundColor Green
Write-Host ""

# Define search directories with easy config at top
$SEARCH_DIRS = @{
    "Core Docs" = "C:\Users\Moses\math_ops\OperatorKernelO6\Core_Docs"
    "Lean Source" = "C:\Users\Moses\math_ops\OperatorKernelO6\OperatorKernelO6"
    "Lean Meta" = "C:\Users\Moses\math_ops\OperatorKernelO6\OperatorKernelO6\Meta"
    "Docs" = "C:\Users\Moses\math_ops\OperatorKernelO6\Docs"
    "Root" = "C:\Users\Moses\math_ops\OperatorKernelO6"
}

# File patterns to search for
$FILE_PATTERNS = @{
    "Lean files (*.lean)" = "*.lean"
    "Markdown docs (*.md)" = "*.md"
    "Text files (*.txt)" = "*.txt"
    "All files (*.*)" = "*.*"
}

Write-Host "AVAILABLE DIRECTORIES:" -ForegroundColor Yellow
$dirKeys = @($SEARCH_DIRS.Keys)
for ($i = 0; $i -lt $dirKeys.Count; $i++) {
    $exists = Test-Path $SEARCH_DIRS[$dirKeys[$i]]
    $status = if ($exists) { "OK" } else { "MISSING" }
    Write-Host "  [$($i + 1)] $status $($dirKeys[$i]) -> $($SEARCH_DIRS[$dirKeys[$i]])" -ForegroundColor White
}
Write-Host ""

# Quick mode for pre-configured combos
if ($QuickMode) {
    Write-Host "QUICK MODE SHORTCUTS:" -ForegroundColor Magenta
    Write-Host "  [Q1] Core Theory Docs (Foundations + Termination + Godel)" -ForegroundColor White
    Write-Host "  [Q2] All Lean Source Files" -ForegroundColor White
    Write-Host "  [Q3] Meta Theory Files Only" -ForegroundColor White
    Write-Host "  [Q4] Documentation Overview" -ForegroundColor White
    Write-Host ""
    $quickChoice = Read-Host "Choose quick preset or Enter for custom"
    
    $AllFiles = @()
    $customTitle = ""
    
    switch ($quickChoice.ToUpper()) {
        "Q1" {
            $PresetFiles = @(
                @{ Path = "C:\Users\Moses\math_ops\OperatorKernelO6\Core_Docs\Operator Centric Foundations of Godelian Incompleteness.md"; Name = "Operator_Centric_Foundations"; Type = "markdown"; DisplayName = "Operator_Centric_Foundations.md"; Description = "Theoretical foundations" }
                @{ Path = "C:\Users\Moses\math_ops\OperatorKernelO6\Core_Docs\Termination_Companion.md"; Name = "Termination_Companion"; Type = "markdown"; DisplayName = "Termination_Companion.md"; Description = "Termination proofs" }
                @{ Path = "C:\Users\Moses\math_ops\OperatorKernelO6\OperatorKernelO6\Meta\Godel.lean"; Name = "Godel_Implementation"; Type = "lean"; DisplayName = "Godel.lean"; Description = "Godel implementation" }
            )
            $customTitle = "Core_Theory_Documentation"
            $AllFiles = $PresetFiles
        }
        "Q2" {
            Get-ChildItem -Path $SEARCH_DIRS["Lean Source"] -Filter "*.lean" -Recurse | ForEach-Object {
                $AllFiles += @{
                    Path = $_.FullName
                    Name = $_.BaseName
                    Type = "lean"
                    DisplayName = "$($_.BaseName).lean"
                    Description = "Lean source file from $($_.DirectoryName)"
                }
            }
            $customTitle = "All_Lean_Source_Files"
        }
        "Q3" {
            if (Test-Path $SEARCH_DIRS["Lean Meta"]) {
                Get-ChildItem -Path $SEARCH_DIRS["Lean Meta"] -Filter "*.lean" -Recurse | ForEach-Object {
                    $AllFiles += @{
                        Path = $_.FullName
                        Name = $_.BaseName
                        Type = "lean"
                        DisplayName = "$($_.BaseName).lean"
                        Description = "Meta-theoretical Lean file"
                    }
                }
            }
            $customTitle = "Meta_Theory_Files"
        }
        "Q4" {
            if (Test-Path $SEARCH_DIRS["Docs"]) {
                Get-ChildItem -Path $SEARCH_DIRS["Docs"] -Filter "*.md" | ForEach-Object {
                    $AllFiles += @{
                        Path = $_.FullName
                        Name = $_.BaseName
                        Type = "markdown"
                        DisplayName = "$($_.BaseName).md"
                        Description = "Project documentation"
                    }
                }
            }
            $customTitle = "Documentation_Overview"
        }
        default {
            Write-Host "Invalid quick choice. Continuing with custom mode..." -ForegroundColor Yellow
        }
    }
    
    if ($AllFiles.Count -gt 0) {
        Write-Host ""
        Write-Host "Quick preset selected: $customTitle" -ForegroundColor Green
        Write-Host "Files included:" -ForegroundColor Cyan
        for ($i = 0; $i -lt $AllFiles.Count; $i++) {
            Write-Host "  [$($i + 1)] $($AllFiles[$i].DisplayName)" -ForegroundColor Gray
        }
        
        $proceed = Read-Host "`nProceed with this selection? (y/n)"
        if ($proceed -eq 'n' -or $proceed -eq 'N') {
            $AllFiles = @()
        }
    }
}

# Manual selection if not using quick mode or quick mode was cancelled
if ($AllFiles.Count -eq 0) {
    Write-Host "SELECT DIRECTORIES TO SEARCH:" -ForegroundColor Yellow
    Write-Host "Enter directory numbers (e.g., 1,3,5 or 1 3 5) or 'all':" -ForegroundColor Green
    $dirSelection = Read-Host "Directories"
    
    # Parse directory selection
    $selectedDirs = @()
    if ($dirSelection.ToLower() -eq 'all') {
        $selectedDirs = $dirKeys
    } else {
        if ($dirSelection -match ',') {
            $selectedNumbers = $dirSelection.Split(',') | ForEach-Object { $_.Trim() }
        } else {
            $selectedNumbers = $dirSelection.Split(' ') | Where-Object { $_ -ne '' } | ForEach-Object { $_.Trim() }
        }
        
        foreach ($num in $selectedNumbers) {
            if ($num -match '^\d+$' -and [int]$num -le $dirKeys.Count -and [int]$num -gt 0) {
                $selectedDirs += $dirKeys[[int]$num - 1]
            }
        }
    }
    
    Write-Host ""
    Write-Host "SELECT FILE TYPES:" -ForegroundColor Yellow
    $patternKeys = @($FILE_PATTERNS.Keys)
    for ($i = 0; $i -lt $patternKeys.Count; $i++) {
        Write-Host "  [$($i + 1)] $($patternKeys[$i])" -ForegroundColor White
    }
    $patternChoice = Read-Host "File type (number)"
    
    if ($patternChoice -match '^\d+$' -and [int]$patternChoice -le $patternKeys.Count -and [int]$patternChoice -gt 0) {
        $selectedPattern = $FILE_PATTERNS[$patternKeys[[int]$patternChoice - 1]]
    } else {
        $selectedPattern = "*.md"
    }
    
    # Scan selected directories for files
    $AllFiles = @()
    foreach ($dirName in $selectedDirs) {
        $dirPath = $SEARCH_DIRS[$dirName]
        if (Test-Path $dirPath) {
            Write-Host "Scanning $dirName..." -ForegroundColor Cyan
            
            Get-ChildItem -Path $dirPath -Filter $selectedPattern -Recurse | ForEach-Object {
                $fileType = switch ($_.Extension) {
                    ".lean" { "lean" }
                    ".md" { "markdown" }
                    ".txt" { "text"} 
                    default { "text" }
                }
                
                $relativePath = $_.FullName.Replace("C:\Users\Moses\math_ops\OperatorKernelO6\", "")
                
                $AllFiles += @{
                    Path = $_.FullName
                    Name = $_.BaseName
                    Type = $fileType
                    DisplayName = "[$($_.BaseName)$($_.Extension)] from $dirName"
                    Description = "File from $relativePath"
                    Directory = $dirName
                }
            }
        } else {
            Write-Host "Directory not found: $dirPath" -ForegroundColor Red
        }
    }
    
    if ($AllFiles.Count -eq 0) {
        Write-Host "No files found matching your criteria!" -ForegroundColor Red
        exit
    }
    
    # Display all found files grouped by directory
    Write-Host ""
    Write-Host "FOUND FILES:" -ForegroundColor Yellow
    $currentDir = ""
    for ($i = 0; $i -lt $AllFiles.Count; $i++) {
        if ($AllFiles[$i].Directory -ne $currentDir) {
            $currentDir = $AllFiles[$i].Directory
            Write-Host ""
            Write-Host "  ${currentDir}:" -ForegroundColor Magenta
        }
        Write-Host "    [$($i + 1)] $($AllFiles[$i].DisplayName)" -ForegroundColor White
    }
    
    Write-Host ""
    Write-Host "SELECT FILES TO CONVERT:" -ForegroundColor Green
    Write-Host "Enter file numbers (e.g., 1,3,5 or 1 3 5) or 'all' for all files:" -ForegroundColor Gray
    $selection = Read-Host "Your selection"
    
    # Parse file selection
    $selectedFiles = @()
    if ($selection.ToLower() -eq 'all') {
        $selectedFiles = $AllFiles
    } else {
        if ($selection -match ',') {
            $selectedNumbers = $selection.Split(',') | ForEach-Object { $_.Trim() }
        } else {
            $selectedNumbers = $selection.Split(' ') | Where-Object { $_ -ne '' } | ForEach-Object { $_.Trim() }
        }
        
        foreach ($num in $selectedNumbers) {
            if ($num -match '^\d+$' -and [int]$num -le $AllFiles.Count -and [int]$num -gt 0) {
                $selectedFiles += $AllFiles[[int]$num - 1]
            }
        }
    }
    
    if ($selectedFiles.Count -eq 0) {
        Write-Host "No valid files selected!" -ForegroundColor Red
        exit
    }
    
    # Show selected files and ask for reordering
    Write-Host ""
    Write-Host "SELECTED FILES (current order):" -ForegroundColor Green
    for ($i = 0; $i -lt $selectedFiles.Count; $i++) {
        Write-Host "  [$($i + 1)] $($selectedFiles[$i].DisplayName)" -ForegroundColor Gray
    }
    
    Write-Host ""
    Write-Host "REORDER FILES? (y/n):" -ForegroundColor Yellow
    $reorder = Read-Host
    
    if ($reorder -eq 'y' -or $reorder -eq 'Y') {
        Write-Host ""
        Write-Host "Enter new order (e.g., 2,1,3 puts second file first):" -ForegroundColor Green
        $newOrder = Read-Host "New order"
        
        $orderNumbers = $newOrder.Split(',') | ForEach-Object { $_.Trim() }
        $reorderedFiles = @()
        
        foreach ($num in $orderNumbers) {
            if ($num -match '^\d+$' -and [int]$num -le $selectedFiles.Count -and [int]$num -gt 0) {
                $reorderedFiles += $selectedFiles[[int]$num - 1]
            }
        }
        
        if ($reorderedFiles.Count -eq $selectedFiles.Count) {
            $selectedFiles = $reorderedFiles
            Write-Host ""
            Write-Host "FILES REORDERED TO:" -ForegroundColor Green
            for ($i = 0; $i -lt $selectedFiles.Count; $i++) {
                Write-Host "  [$($i + 1)] $($selectedFiles[$i].DisplayName)" -ForegroundColor Gray
            }
        } else {
            Write-Host "Invalid reorder sequence. Using original order." -ForegroundColor Yellow
        }
    }
    
    # Get custom title
    Write-Host ""
    Write-Host "CUSTOM TITLE for combined document:" -ForegroundColor Yellow
    $customTitle = Read-Host "Title (or press Enter for auto-generated)"
    if ([string]::IsNullOrWhiteSpace($customTitle)) {
        $dirNames = ($selectedFiles | Select-Object -Property Directory -Unique | ForEach-Object { $_.Directory }) -join "_"
        $customTitle = "Custom_Selection_$dirNames"
    }
    
    $AllFiles = $selectedFiles
}

Write-Host ""
Write-Host "CONVERTING YOUR SELECTION..." -ForegroundColor Cyan
Write-Host "Output directory: $OutputDir" -ForegroundColor Gray
Write-Host ""

# Create output directory
New-Item -ItemType Directory -Path $OutputDir -Force | Out-Null

# Load System.Web for HTML encoding
Add-Type -AssemblyName System.Web

# Function to convert HTML to PDF
function Convert-HtmlToPdf {
    param([string]$HtmlPath, [string]$PdfPath)
    
    $wkhtmltopdf = $null
    $possiblePaths = @(
        "wkhtmltopdf",
        "C:\Program Files\wkhtmltopdf\bin\wkhtmltopdf.exe",
        "C:\Program Files (x86)\wkhtmltopdf\bin\wkhtmltopdf.exe",
        "$env:LOCALAPPDATA\Programs\wkhtmltopdf\bin\wkhtmltopdf.exe"
    )
    
    foreach ($path in $possiblePaths) {
        if (Get-Command $path -ErrorAction SilentlyContinue) {
            $wkhtmltopdf = $path
            break
        }
        if (Test-Path $path) {
            $wkhtmltopdf = $path
            break
        }
    }
    
    if ($wkhtmltopdf) {
        try {
            & $wkhtmltopdf --page-size A4 --margin-top 0.5in --margin-bottom 0.5in --margin-left 0.5in --margin-right 0.5in --enable-local-file-access --print-media-type "$HtmlPath" "$PdfPath" 2>$null
            return $true
        } catch {
            return $false
        }
    }
    return $false
}

# Function to convert markdown to HTML
function Convert-MarkdownToHtml {
    param([string]$MarkdownContent)
    
    $html = $MarkdownContent
    
    # Fix escaped markdown
    $html = $html -replace '\\##', '##'
    $html = $html -replace '\\#', '#'
    $html = $html -replace '\\\*', '*'
    $html = $html -replace '\\`', '`'
    
    # Headers
    $html = $html -replace '(?m)^### (.*)', '<h3>$1</h3>'
    $html = $html -replace '(?m)^## (.*)', '<h2>$1</h2>'
    $html = $html -replace '(?m)^# (.*)', '<h1 class="section-header">$1</h1>'
    
    # Bold and italic
    $html = $html -replace '\*\*(.*?)\*\*', '<strong>$1</strong>'
    $html = $html -replace '\*(.*?)\*', '<em>$1</em>'
    
    # Code blocks
    $html = $html -replace '(?s)```(\w+)?\s*\n(.*?)\n```', '<pre><code class="$1">$2</code></pre>'
    
    # Inline code
    $html = $html -replace '`([^`]+)`', '<code>$1</code>'
    
    # Links
    $html = $html -replace '\[([^\]]+)\]\(([^)]+)\)', '<a href="$2">$1</a>'
    
    # Line breaks
    $html = $html -replace '(?m)\n\n+', '</p><p>'
    $html = "<p>$html</p>"
    $html = $html -replace '<p></p>', ''
    
    # Lists
    $html = $html -replace '(?m)^[\*\-] (.*)', '<li>$1</li>'
    $html = $html -replace '(<li>.*?</li>)', '<ul>$1</ul>'
    
    return $html
}

# Function to generate HTML content
function Generate-HtmlContent {
    param(
        [string]$Title,
        [string]$Content,
        [string]$Description = "",
        [string]$FilePath = "",
        [string]$FileType = "lean"
    )
    
    $Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    
    if ($FileType -eq "markdown") {
        $ProcessedContent = Convert-MarkdownToHtml -MarkdownContent $Content
        $ContentSection = "<div class='markdown-content'>$ProcessedContent</div>"
    } else {
        $EscapedContent = [System.Web.HttpUtility]::HtmlEncode($Content)
        $ContentSection = "<pre><code class='$FileType'>$EscapedContent</code></pre>"
    }
    
    return @"
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>$Title - OperatorKernelO6</title>
    <style>
        body {
            max-width: 1200px;
            margin: 0 auto;
            padding: 30px;
            font-family: system-ui, -apple-system, sans-serif;
            font-size: 16px;
            line-height: 1.6;
            color: #333;
            background: #fff;
        }
        
        h1 {
            color: #2c3e50;
            border-bottom: 3px solid #3498db;
            padding-bottom: 10px;
            margin-bottom: 30px;
            font-size: 2.5em;
        }
        
        h2 {
            color: #34495e;
            border-bottom: 2px solid #bdc3c7;
            margin-top: 40px;
            padding-bottom: 8px;
            font-size: 1.8em;
        }
        
        h3 {
            color: #2c3e50;
            margin-top: 30px;
            font-size: 1.4em;
        }
        
        .metadata {
            background: #e8f4fd;
            padding: 20px;
            border-radius: 8px;
            border-left: 5px solid #3498db;
            margin: 25px 0;
        }
        
        .description {
            background: #f0f8f0;
            padding: 20px;
            border-radius: 8px;
            border-left: 5px solid #27ae60;
            margin: 25px 0;
        }
        
        pre {
            background: #f8f9fa;
            padding: 20px;
            border-radius: 8px;
            overflow-x: auto;
            border: 1px solid #dee2e6;
            font-size: 14px;
            line-height: 1.4;
            white-space: pre-wrap;
            word-wrap: break-word;
            font-family: 'Consolas', 'Monaco', 'Courier New', monospace;
        }
        
        code {
            background: #f1f2f6;
            padding: 3px 6px;
            border-radius: 4px;
            font-family: 'Consolas', 'Monaco', 'Courier New', monospace;
            font-size: 0.9em;
        }
        
        .markdown-content p {
            margin-bottom: 15px;
            line-height: 1.7;
        }
        
        .markdown-content ul {
            margin: 15px 0;
            padding-left: 30px;
        }
        
        .markdown-content li {
            margin-bottom: 8px;
        }
        
        .markdown-content a {
            color: #3498db;
            text-decoration: none;
        }
        
        .markdown-content a:hover {
            text-decoration: underline;
        }
        
        @media print {
            body {
                max-width: none;
                margin: 0;
                padding: 15px;
                font-size: 14px;
            }
            
            h1 { font-size: 20px; }
            h2 { font-size: 16px; }
            h3 { font-size: 14px; }
            
            pre {
                font-size: 11px;
                line-height: 1.3;
                padding: 10px;
            }
        }
    </style>
</head>
<body>
    <h1>$Title</h1>
    
    <div class="metadata">
        <p>
            <strong>File:</strong> <code>$FilePath</code><br>
            <strong>Type:</strong> $FileType<br>
            <strong>Generated:</strong> $Timestamp<br>
            <strong>Size:</strong> $($Content.Length) characters
        </p>
    </div>
    
    $(if ($Description) { "<div class='description'><h3>Overview</h3><p>$Description</p></div>" })
    
    $(if ($FileType -eq "markdown") { "<h2>Document Content</h2>" } else { "<h2>Source Code</h2>" })
    $ContentSection
    
    <script>
        // Syntax highlighting for Lean code
        document.addEventListener('DOMContentLoaded', function() {
            const codeElements = document.querySelectorAll('pre code.lean');
            codeElements.forEach(function(codeElement) {
                let content = codeElement.innerHTML;
                
                const keywords = [
                    'import', 'namespace', 'end', 'theorem', 'lemma', 'def', 'noncomputable',
                    'by', 'have', 'exact', 'simpa', 'simp', 'calc', 'cases', 'with',
                    'intro', 'apply', 'rw', 'sorry', 'private', 'open', 'universe',
                    'set_option', 'attribute', 'inductive', 'structure', 'class', 'instance'
                ];
                
                keywords.forEach(keyword => {
                    const regex = new RegExp('\\\\b' + keyword + '\\\\b', 'g');
                    content = content.replace(regex, '<span style="color: #0066cc; font-weight: bold;">' + keyword + '</span>');
                });
                
                // Comments
                content = content.replace(/--[^\\n]*/g, '<span style="color: #008000; font-style: italic;">$$&</span>');
                
                // Highlight sorry
                content = content.replace(/\\bsorry\\b/g, '<span style="background: #ffcccc; color: #cc0000; font-weight: bold; padding: 1px 3px; border-radius: 2px;">sorry</span>');
                
                codeElement.innerHTML = content;
            });
        });
    </script>
</body>
</html>
"@
}

# Process each selected file
$ProcessedFiles = @()
foreach ($file in $AllFiles) {
    Write-Host "Processing: $($file.DisplayName)" -ForegroundColor Cyan
    
    if (!(Test-Path $file.Path)) {
        Write-Host "  File not found: $($file.Path)" -ForegroundColor Red
        continue
    }
    
    try {
        $FileContent = Get-Content $file.Path -Raw -Encoding UTF8
        if ([string]::IsNullOrWhiteSpace($FileContent)) {
            $FileContent = "-- File appears to be empty or could not be read properly"
        }
    } catch {
        Write-Host "  Could not read file: $($_.Exception.Message)" -ForegroundColor Red
        continue
    }
    
    # Create individual HTML and PDF
    $SafeName = $file.Name -replace '[^\w\-_]', '_'
    $HtmlFile = Join-Path $OutputDir "$SafeName.html"
    $PdfFile = Join-Path $OutputDir "$SafeName.pdf"
    
    $HtmlContent = Generate-HtmlContent -Title $file.Name -Content $FileContent -Description $file.Description -FilePath $file.Path -FileType $file.Type
    
    try {
        $HtmlContent | Out-File -FilePath $HtmlFile -Encoding UTF8
        Write-Host "  HTML: $SafeName.html" -ForegroundColor Green
        
        if (Convert-HtmlToPdf -HtmlPath $HtmlFile -PdfPath $PdfFile) {
            Write-Host "  PDF: $SafeName.pdf" -ForegroundColor Green
        } else {
            Write-Host "  PDF creation failed for $SafeName" -ForegroundColor Yellow
        }
        
        $ProcessedFiles += @{
            Name = $file.Name
            Content = $FileContent
            Description = $file.Description
            FilePath = $file.Path
            FileType = $file.Type
        }
    } catch {
        Write-Host "  Could not create files: $($_.Exception.Message)" -ForegroundColor Red
    }
}

# Create combined document if multiple files
if ($ProcessedFiles.Count -gt 1) {
    Write-Host ""
    Write-Host "Creating combined document: $customTitle" -ForegroundColor Cyan
    
    $CombinedContent = ""
    $TableOfContents = ""
    
    foreach ($file in $ProcessedFiles) {
        $TableOfContents += "- [$($file.Name)]($($file.FilePath))`n"
        $CombinedContent += "`n`n# $($file.Name)`n`n"
        if ($file.Description) {
            $CombinedContent += "**Description:** $($file.Description)`n`n"
        }
        $CombinedContent += "**File:** ``$($file.FilePath)```n`n"
        $CombinedContent += "``````$($file.FileType.ToLower())`n"
        $CombinedContent += $file.Content
        $CombinedContent += "`n``````"
        $CombinedContent += "`n`n---"
    }
    
    $FullCombinedContent = "# $customTitle`n`nCustom selection and ordering of project files.`n`n## Table of Contents`n`n$TableOfContents`n$CombinedContent"
    
    $SafeTitle = $customTitle -replace '[^\w\-_]', '_'
    $HtmlFile = Join-Path $OutputDir "$SafeTitle.html"
    $PdfFile = Join-Path $OutputDir "$SafeTitle.pdf"
    
    $HtmlContent = Generate-HtmlContent -Title $customTitle -Content $FullCombinedContent -Description "Custom selection and ordering of project files" -FilePath "Combined Document" -FileType "markdown"
    
    try {
        $HtmlContent | Out-File -FilePath $HtmlFile -Encoding UTF8
        Write-Host "  Combined HTML: $SafeTitle.html" -ForegroundColor Green
        
        if (Convert-HtmlToPdf -HtmlPath $HtmlFile -PdfPath $PdfFile) {
            Write-Host "  Combined PDF: $SafeTitle.pdf" -ForegroundColor Green
        }
    } catch {
        Write-Host "  Could not create combined files: $($_.Exception.Message)" -ForegroundColor Red
    }
}

Write-Host ""
Write-Host "FLEXIBLE CONVERSION COMPLETE!" -ForegroundColor Green
Write-Host "Output directory: $OutputDir" -ForegroundColor White
Write-Host ""

Write-Host "SUMMARY:" -ForegroundColor Cyan
Write-Host "  Individual files processed: $($ProcessedFiles.Count)" -ForegroundColor Gray
if ($ProcessedFiles.Count -gt 1) {
    Write-Host "  Combined document created: $customTitle" -ForegroundColor Gray
}

Write-Host ""
Write-Host "USAGE TIPS:" -ForegroundColor Yellow
Write-Host "  • Use -QuickMode for preset combinations" -ForegroundColor White
Write-Host "  • Modify SEARCH_DIRS at top of script to add directories" -ForegroundColor White
Write-Host "  • All files are saved as both HTML and PDF" -ForegroundColor White