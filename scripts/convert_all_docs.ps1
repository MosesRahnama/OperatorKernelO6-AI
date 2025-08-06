param(
    [string]$OutputDir = "",
    [switch]$LeanOnly,
    [switch]$CoreDocsOnly,
    [string[]]$CoreDocsOrder = @('Guide', 'Foundations', 'Agent')  # SET YOUR DEFAULT COMBO HERE!
)

# Set default paths
if ($OutputDir -eq "") {
    $OutputDir = "c:\Users\Moses\math_ops\OperatorKernelO6\docs"
}

# Create output directory
New-Item -ItemType Directory -Path $OutputDir -Force | Out-Null

Write-Host "=== OperatorKernelO6 Documentation Generator ===" -ForegroundColor Cyan
Write-Host "Output directory: $OutputDir" -ForegroundColor Gray

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

# Function to convert markdown to HTML - AB FAB VERSION!
function Convert-MarkdownToHtml {
    param([string]$MarkdownContent)
    
    # Enhanced markdown converter with proper escaping
    $html = $MarkdownContent
    
    # Fix escaped markdown first - CRITICAL FOR AB FAB!
    $html = $html -replace '\\##', '##'
    $html = $html -replace '\\#', '#'  
    $html = $html -replace '\\\*', '*'
    $html = $html -replace '\\`', '`'
    
    # Headers (with proper academic styling)
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
    
    # Tables (basic support)
    $html = $html -replace '(?m)^\|(.+)\|$', '<tr><td>$1</td></tr>'
    
    # Line breaks (convert double newlines to paragraphs)
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
    
    # Extract proper title from markdown content for AB FAB formatting
    $ActualTitle = $Title
    if ($FileType -eq "markdown" -and $Content -match '(?m)^# (.+)') {
        $ActualTitle = $matches[1] -replace '\\#', '#' -replace '\\', ''
    }
    
    # Handle markdown vs code content differently
    if ($FileType -eq "markdown") {
        $ProcessedContent = Convert-MarkdownToHtml -MarkdownContent $Content
        # Remove the first h1 since we'll use it as the main title
        $ProcessedContent = $ProcessedContent -replace '<h1 class="section-header">.*?</h1>', ''
        $ContentSection = "<div class='markdown-content'>$ProcessedContent</div>"
    } else {
        $EscapedContent = [System.Web.HttpUtility]::HtmlEncode($Content)
        $ContentSection = "<pre><code class='lean'>$EscapedContent</code></pre>"
    }
    
    return @"
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>$ActualTitle</title>
    <style>
        /* ACADEMIC JOURNAL TUX STYLING */
        body {
            max-width: 210mm;
            margin: 0 auto;
            padding: 25mm 20mm;
            font-family: 'Times New Roman', 'Times', serif;
            font-size: 11pt;
            line-height: 1.6;
            color: #000;
            background: #fff;
            text-align: justify;
            hyphens: auto;
        }
        
        /* JOURNAL TITLE STYLING */
        h1 {
            font-size: 18pt;
            font-weight: bold;
            text-align: center;
            margin: 0 0 6pt 0;
            color: #000;
            border: none;
            text-transform: none;
        }
        
        /* SECTION HEADERS */
        h2 {
            font-size: 12pt;
            font-weight: bold;
            margin: 18pt 0 6pt 0;
            color: #000;
            border: none;
            text-transform: uppercase;
            letter-spacing: 0.5pt;
        }
        
        h3 {
            font-size: 11pt;
            font-weight: bold;
            margin: 12pt 0 6pt 0;
            color: #000;
            font-style: italic;
        }
        
        /* ACADEMIC AUTHOR/ABSTRACT STYLING */
        .metadata {
            text-align: center;
            margin: 12pt 0 18pt 0;
            font-size: 10pt;
            border: none;
            background: none;
            padding: 0;
        }
        
        .metadata strong {
            font-weight: normal;
            font-variant: small-caps;
        }
        
        .description {
            margin: 18pt 0;
            padding: 12pt;
            background: #f9f9f9;
            border: 1pt solid #ddd;
            font-size: 10pt;
        }
        
        .description h3 {
            margin: 0 0 6pt 0;
            font-size: 11pt;
            font-weight: bold;
            color: #000;
        }
        
        /* ACADEMIC CODE/FORMULA BLOCKS */
        pre {
            background: #fafafa;
            padding: 12pt;
            margin: 12pt 0;
            border: 0.5pt solid #ccc;
            font-family: 'Courier New', 'Monaco', monospace;
            font-size: 9pt;
            line-height: 1.3;
            overflow-x: auto;
            text-align: left;
        }
        
        /* INLINE CODE */
        code {
            font-family: 'Courier New', 'Monaco', monospace;
            font-size: 9pt;
            background: #f5f5f5;
            padding: 1pt 2pt;
            border: 0.5pt solid #ddd;
        }
        
        /* Markdown-specific styles */
        .markdown-content h1, .markdown-content h2, .markdown-content h3 {
            color: #2c3e50;
            margin-top: 30px;
            margin-bottom: 15px;
        }
        
        .markdown-content h1 {
            border-bottom: 2px solid #3498db;
            padding-bottom: 10px;
        }
        
        .markdown-content h2 {
            border-bottom: 1px solid #bdc3c7;
            padding-bottom: 5px;
        }
        
        .markdown-content p {
            margin-bottom: 15px;
            line-height: 1.6;
        }
        
        .markdown-content ul {
            margin: 15px 0;
            padding-left: 30px;
        }
        
        .markdown-content li {
            margin-bottom: 8px;
            line-height: 1.5;
        }
        
        .markdown-content code {
            background: #f1f2f6;
            padding: 2px 6px;
            border-radius: 3px;
            font-family: 'Consolas', 'Monaco', 'Courier New', monospace;
            font-size: 0.9em;
        }
        
        .markdown-content pre {
            background: #f8f9fa;
            padding: 15px;
            border-radius: 5px;
            overflow-x: auto;
            border: 1px solid #dee2e6;
        }
        
        .markdown-content a {
            color: #3498db;
            text-decoration: none;
        }
        
        .markdown-content a:hover {
            text-decoration: underline;
        }
        
        .markdown-content strong {
            font-weight: 600;
        }
        
        .markdown-content em {
            font-style: italic;
        }
        
        @media print {
            body {
                width: 100%;
                max-width: none;
                margin: 0;
                padding: 15px;
                font-size: 16px;
            }
            pre {
                font-size: 13px;
                line-height: 1.35;
                margin: 15px 0;
                padding: 15px;
                background: #f8f9fa !important;
                border: 1px solid #dee2e6 !important;
                width: 100%;
                box-sizing: border-box;
            }
            h1 {
                font-size: 24px;
                margin-bottom: 20px;
            }
            h2 {
                font-size: 20px;
                margin-top: 25px;
            }
            .metadata, .description {
                margin: 15px 0;
                padding: 12px;
            }
        }
        
        @page {
            margin: 0.5in;
            size: letter;
        }
    </style>
</head>
<body>
    <h1>$ActualTitle</h1>
    
    <div class="metadata">
        <p>
            <strong>Moses Rahnama</strong><br>
            <em>Mina Analytics</em><br>
            <strong>Generated:</strong> $Timestamp
        </p>
    </div>
    
    $(if ($Description) { "<div class='description'><h3>Overview</h3><p>$Description</p></div>" })
    
    $(if ($FileType -eq "markdown") { "<h2>Document Content</h2>" } else { "<h2>Source Code</h2>" })
    $ContentSection
    
    <script>
        document.addEventListener('DOMContentLoaded', function() {
            const codeElement = document.querySelector('pre code');
            if (codeElement && codeElement.classList.contains('lean')) {
                let content = codeElement.innerHTML;
                
                const keywords = [
                    'import', 'namespace', 'end', 'theorem', 'lemma', 'def', 'noncomputable',
                    'by', 'have', 'exact', 'simpa', 'simp', 'calc', 'cases', 'with',
                    'intro', 'apply', 'rw', 'sorry', 'private', 'open', 'universe',
                    'set_option', 'attribute', 'inductive', 'structure', 'class', 'instance'
                ];
                
                keywords.forEach(keyword => {
                    const regex = new RegExp('\\b' + keyword + '\\b', 'g');
                    content = content.replace(regex, '<span style="color: #0066cc; font-weight: bold;">' + keyword + '</span>');
                });
                
                content = content.replace(/--[^\n]*/g, '<span style="color: #008000; font-style: italic;">$&</span>');
                content = content.replace(/\bsorry\b/g, '<span style="background: #ffcccc; color: #cc0000; font-weight: bold; padding: 1px 3px; border-radius: 2px;">sorry</span>');
                
                codeElement.innerHTML = content;
            }
        });
    </script>
</body>
</html>
"@
}

# Function to process a single file
function Process-File {
    param(
        [string]$FilePath,
        [string]$OutputName,
        [string]$Description = "",
        [string]$FileType = "lean"
    )
    
    if (!(Test-Path $FilePath)) {
        Write-Host "  [SKIP] File not found: $FilePath" -ForegroundColor Red
        return $null
    }
    
    try {
        $FileContent = Get-Content $FilePath -Raw -Encoding UTF8
        if ([string]::IsNullOrWhiteSpace($FileContent)) {
            $FileContent = "-- File appears to be empty or could not be read properly"
        }
    } catch {
        Write-Host "  [ERROR] Could not read file: $($_.Exception.Message)" -ForegroundColor Red
        return $null
    }
    
    $HtmlFile = Join-Path $OutputDir "$OutputName.html"
    $PdfFile = Join-Path $OutputDir "$OutputName.pdf"
    
    $HtmlContent = Generate-HtmlContent -Title $OutputName -Content $FileContent -Description $Description -FilePath $FilePath -FileType $FileType
    
    try {
        $HtmlContent | Out-File -FilePath $HtmlFile -Encoding UTF8
        Write-Host "  [SUCCESS] HTML: $OutputName.html" -ForegroundColor Green
        
        if (Convert-HtmlToPdf -HtmlPath $HtmlFile -PdfPath $PdfFile) {
            Write-Host "  [SUCCESS] PDF: $OutputName.pdf" -ForegroundColor Green
        } else {
            Write-Host "  [WARN] PDF creation failed for $OutputName" -ForegroundColor Yellow
        }
        
        return @{
            Name = $OutputName
            Content = $FileContent
            Description = $Description
            FilePath = $FilePath
            FileType = $FileType
        }
    } catch {
        Write-Host "  [ERROR] Could not create files: $($_.Exception.Message)" -ForegroundColor Red
        return $null
    }
}

# Function to create combined document
function Create-CombinedDocument {
    param(
        [array]$Files,
        [string]$CombinedName,
        [string]$CombinedDescription
    )
    
    $CombinedContent = ""
    $TableOfContents = ""
    
    foreach ($file in $Files) {
        if ($file) {
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
    }
    
    $FullCombinedContent = "# $CombinedName`n`n$CombinedDescription`n`n## Table of Contents`n`n$TableOfContents`n$CombinedContent"
    
    $HtmlFile = Join-Path $OutputDir "$CombinedName.html"
    $PdfFile = Join-Path $OutputDir "$CombinedName.pdf"
    
    $HtmlContent = Generate-HtmlContent -Title $CombinedName -Content $FullCombinedContent -Description $CombinedDescription -FilePath "Combined Document" -FileType "markdown"
    
    try {
        $HtmlContent | Out-File -FilePath $HtmlFile -Encoding UTF8
        Write-Host "  [SUCCESS] Combined HTML: $CombinedName.html" -ForegroundColor Green
        
        if (Convert-HtmlToPdf -HtmlPath $HtmlFile -PdfPath $PdfFile) {
            Write-Host "  [SUCCESS] Combined PDF: $CombinedName.pdf" -ForegroundColor Green
        }
    } catch {
        Write-Host "  [ERROR] Could not create combined files: $($_.Exception.Message)" -ForegroundColor Red
    }
}

# Process Lean files (if not CoreDocsOnly)
if (!$CoreDocsOnly) {
    Write-Host "`n=== Processing Lean Files ===" -ForegroundColor Yellow
    

    
    $ProcessedLeanFiles = @()
    foreach ($FileInfo in $LeanFiles) {
        Write-Host "Processing: $($FileInfo.Name)" -ForegroundColor Cyan
        $result = Process-File -FilePath $FileInfo.Path -OutputName $FileInfo.Name -Description $FileInfo.Description -FileType "lean"
        if ($result) {
            $ProcessedLeanFiles += $result
        }
    }
    
    Write-Host "`nCreating combined Lean documentation..." -ForegroundColor Cyan
    Create-CombinedDocument -Files $ProcessedLeanFiles -CombinedName "OperatorKernelO6_Complete_Lean_Documentation" -CombinedDescription "Complete documentation of all Lean files in the OperatorKernelO6 project, including core kernel definitions and meta-theoretical proofs."
}

# Process Core Docs (if not LeanOnly)
if (!$LeanOnly) {
    Write-Host "`n=== Processing Core Documentation ===" -ForegroundColor Yellow
    
    $CoreDocsFiles = @(
        # @{ Path = "C:\Users\Moses\math_ops\OperatorKernelO6\core_docs\OperatorKernelO6_COMPLETE_GUIDE.md"; Name = "Complete_Guide"; Description = "Comprehensive guide to OperatorKernelO6" },
        @{ Path = "C:\Users\Moses\math_ops\OperatorKernelO6\core_docs\Operator Centric Foundations of Godelian Incompleteness.md"; Name = "Operator_Centric_Foundations"; Description = "Theoretical foundations of operator-centric approach to Gödel's incompleteness" },
        @{ Path = "C:\Users\Moses\math_ops\OperatorKernelO6\core_docs\Termination_Companion.md"; Name = "Termination_Companion"; Description = "Companion document for termination proofs" },
        # @{ Path = "C:\Users\Moses\math_ops\OperatorKernelO6\core_docs\agent.md"; Name = "Agent"; Description = "Agent-based documentation and processes" }
        # @{ Path = "C:\Users\Moses\math_ops\OperatorKernelO6\core_docs\O3-Pro-Jul-22"; Name = "O3-Pro"; Description = "cO3-Pro-Jul-22-Aug-4" }
        @{ Path = "C:\Users\Moses\math_ops\OperatorKernelO6\core_docs\ordinal-toolkit.md"; Name = "ordinal-toolkit"; Description = "ordinal-op-toolkit" }
    )
    
    $ProcessedCoreFiles = @()
    foreach ($FileInfo in $CoreDocsFiles) {
        Write-Host "Processing: $($FileInfo.Name)" -ForegroundColor Cyan
        $result = Process-File -FilePath $FileInfo.Path -OutputName $FileInfo.Name -Description $FileInfo.Description -FileType "markdown"
        if ($result) {
            $ProcessedCoreFiles += $result
        }
    }
    
    # Create custom combined docs if order specified
    if ($CoreDocsOrder.Count -gt 0) {
        Write-Host "`nCreating custom combined core documentation..." -ForegroundColor Cyan
        $OrderedFiles = @()
        foreach ($orderName in $CoreDocsOrder) {
            $matchedFile = $ProcessedCoreFiles | Where-Object { $_.Name -like "*$orderName*" }
            if ($matchedFile) {
                $OrderedFiles += $matchedFile
            }
        }
        Create-CombinedDocument -Files $OrderedFiles -CombinedName "Custom_Core_Documentation" -CombinedDescription "Custom selection and ordering of core documentation files."
    } else {
        Write-Host "`nCreating complete combined core documentation..." -ForegroundColor Cyan
        Create-CombinedDocument -Files $ProcessedCoreFiles -CombinedName "Complete_Core_Documentation" -CombinedDescription "Complete documentation of all core documentation files in the OperatorKernelO6 project."
    }
    
    Write-Host "`n=== Custom Core Docs Usage ===" -ForegroundColor Magenta
    Write-Host "To create custom combinations, use:" -ForegroundColor White
    Write-Host "  .\convert_all_docs.ps1 -CoreDocsOrder @('Guide', 'Foundations', 'Agent')" -ForegroundColor Gray
    Write-Host "Available files: Complete_Guide, Operator_Centric_Foundations, Termination_Companion, Agent" -ForegroundColor Gray
}

Write-Host "`n=== Documentation Generation Complete! ===" -ForegroundColor Green
Write-Host "Files created in: $OutputDir" -ForegroundColor White

Get-ChildItem -Path $OutputDir -Filter "*.html" | ForEach-Object {
    Write-Host "  HTML: $($_.Name)" -ForegroundColor Gray
}
Get-ChildItem -Path $OutputDir -Filter "*.pdf" | ForEach-Object {
    Write-Host "  PDF: $($_.Name)" -ForegroundColor Gray
}