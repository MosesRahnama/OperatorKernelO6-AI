param(
    [string]$InputFile = "",
    [string]$OutputDir = ""
)

# Set default paths
if ($OutputDir -eq "") {
    $OutputDir = "c:\Users\Moses\math_ops\OperatorKernelO6\docs"
}

# Define the files we want to convert (only the real project files)
$FilesToConvert = @(
    @{
        Path = "c:\Users\Moses\math_ops\OperatorKernelO6\OperatorKernelO6\Kernel.lean"
        Name = "Kernel"
        Description = "Core trace definitions and reduction rules"
    },
    @{
        Path = "c:\Users\Moses\math_ops\OperatorKernelO6\OperatorKernelO6\Meta\Termination.lean"
        Name = "Termination"
        Description = "Complete termination proof with ordinal measures and mu_decreases theorem"
    }
)

# If specific file provided, only convert that one
if ($InputFile -ne "") {
    $FilesToConvert = @(@{
        Path = $InputFile
        Name = [System.IO.Path]::GetFileNameWithoutExtension($InputFile)
        Description = "User-specified file"
    })
}

# Create output directory
New-Item -ItemType Directory -Path $OutputDir -Force | Out-Null

Write-Host "Converting Lean files to documentation..." -ForegroundColor Green
Write-Host "Output directory: $OutputDir" -ForegroundColor Gray

# Load System.Web for HTML encoding
Add-Type -AssemblyName System.Web

foreach ($FileInfo in $FilesToConvert) {
    $FilePath = $FileInfo.Path
    $FileName = $FileInfo.Name
    $FileDescription = $FileInfo.Description
    
    Write-Host ""
    Write-Host "Processing: $FileName" -ForegroundColor Yellow
    Write-Host "Path: $FilePath" -ForegroundColor Gray
    
    # Check if file exists
    if (!(Test-Path $FilePath)) {
        Write-Host "  [SKIP] File not found: $FilePath" -ForegroundColor Red
        continue
    }
    
    # Read file content
    try {
        $FileContent = Get-Content $FilePath -Raw -Encoding UTF8
        if ([string]::IsNullOrWhiteSpace($FileContent)) {
            Write-Host "  [WARN] File appears to be empty" -ForegroundColor Yellow
            $FileContent = "-- File appears to be empty or could not be read properly"
        }
        Write-Host "  [OK] Read $($FileContent.Length) characters" -ForegroundColor Green
    } catch {
        Write-Host "  [ERROR] Could not read file: $($_.Exception.Message)" -ForegroundColor Red
        continue
    }
    
    # Generate timestamp
    $Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    
    # Create HTML output
    $HtmlFile = Join-Path $OutputDir "$FileName`_Documentation.html"
    
    # Properly encode the file content for HTML
    $EscapedContent = [System.Web.HttpUtility]::HtmlEncode($FileContent)
    
    $HtmlContent = @"
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>$FileName Analysis - OperatorKernelO6</title>
    <style>
        body {
            width: 100vw;         /* full width */
            max-width: none;
            margin: 0;
            padding: 20px;
            font-size: 18px;      /* larger default font */
            color: #333;
            background: #fff;
        }
        
        h1 {
            color: #2c3e50;
            border-bottom: 3px solid #3498db;
            padding-bottom: 10px;
            margin-bottom: 30px;
        }
        
        h2 {
            color: #34495e;
            border-bottom: 1px solid #bdc3c7;
            margin-top: 40px;
            padding-bottom: 5px;
        }
        
        .metadata {
            background: #e8f4fd;
            padding: 15px;
            border-radius: 8px;
            border-left: 4px solid #3498db;
            margin: 20px 0;
        }
        
        .description {
            background: #f0f8f0;
            padding: 15px;
            border-radius: 8px;
            border-left: 4px solid #27ae60;
            margin: 20px 0;
        }
        
        pre {
            background: #f8f9fa;
            padding: 20px;
            border-radius: 8px;
            overflow-x: auto;
            border: 1px solid #dee2e6;
            font-size: 14px;      /* larger code font */
            line-height: 1.4;
            white-space: pre-wrap;
            word-wrap: break-word;
            font-family: 'Consolas', 'Monaco', 'Courier New', monospace;
        }
        
        code {
            font-family: 'Consolas', 'Monaco', 'Courier New', monospace;
            background: #f1f2f6;
            padding: 2px 4px;
            border-radius: 3px;
            font-size: 85%;
        }
        
        .print-instructions {
            background: #fff3cd;
            padding: 15px;
            border-radius: 8px;
            border-left: 4px solid #ffc107;
            margin-top: 40px;
        }
        
        kbd {
            background: #333;
            color: white;
            padding: 2px 6px;
            border-radius: 3px;
            font-size: 12px;
        }
        
        @media print {
            body {
                width: 100%;
                max-width: none;
                margin: 0;
                padding: 15px;
                font-size: 16px;  /* larger base font for PDF */
            }
            pre {
                font-size: 13px;  /* larger code font */
                line-height: 1.35;
                margin: 15px 0;
                padding: 15px;
                background: #f8f9fa !important;
                border: 1px solid #dee2e6 !important;
                width: 100%;
                box-sizing: border-box;
            }
            code {
                font-size: 13px;  /* match pre font size */
            }
            .print-instructions {
                display: none;
            }
            h1, h2 {
                page-break-after: avoid;
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
            margin: 0.5in;  /* smaller margins for more content space */
            size: letter;
        }
    </style>
</head>
<body>
    <h1>$FileName Analysis - OperatorKernelO6</h1>
    
    <div class="metadata">
        <p>
            <strong>File:</strong> <code>OperatorKernelO6/$($FilePath.Split('\')[-2..-1] -join '\')</code><br>
            <strong>Author:</strong> Moses<br>
            <strong>Generated:</strong> $Timestamp<br>
            <strong>File Size:</strong> $($FileContent.Length) characters
        </p>
    </div>
    
    <div class="description">
        <h3>Overview</h3>
        <p>$FileDescription</p>
    </div>
    
    <h2>Source Code</h2>
    <pre><code>$EscapedContent</code></pre>
    
    <div class="print-instructions">
        <h3>Print to PDF Instructions</h3>
        <ol>
            <li>Press <kbd>Ctrl+P</kbd> to open the print dialog</li>
            <li>Choose "Save as PDF" or "Microsoft Print to PDF"</li>
            <li>Set margins to "Minimum" or "Custom" with 0.5 inch margins</li>
            <li>Enable "Background graphics" to preserve colors</li>
            <li>Set scale to "Fit to page width" if needed</li>
        </ol>
        <p><strong>Note:</strong> The code section will automatically wrap lines for better printing.</p>
    </div>
    
    <script>
        // Simple syntax highlighting for Lean keywords
        document.addEventListener('DOMContentLoaded', function() {
            const codeElement = document.querySelector('pre code');
            if (codeElement) {
                let content = codeElement.innerHTML;
                
                // Highlight Lean keywords
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
                
                // Highlight comments
                content = content.replace(/--[^\n]*/g, '<span style="color: #008000; font-style: italic;">$&</span>');
                
                // Highlight sorry with red background
                content = content.replace(/\bsorry\b/g, '<span style="background: #ffcccc; color: #cc0000; font-weight: bold; padding: 1px 3px; border-radius: 2px;">sorry</span>');
                
                codeElement.innerHTML = content;
            }
        });
    </script>
</body>
</html>
"@

    # Write HTML file
    try {
        $HtmlContent | Out-File -FilePath $HtmlFile -Encoding UTF8
        Write-Host "  [SUCCESS] HTML created: $HtmlFile" -ForegroundColor Green
    } catch {
        Write-Host "  [ERROR] Could not create HTML: $($_.Exception.Message)" -ForegroundColor Red
        continue
    }
    
    # Convert HTML to PDF
    Write-Host "  [INFO] Creating PDF from HTML..." -ForegroundColor Cyan
    $PdfFile = Join-Path $OutputDir "$FileName`_Documentation.pdf"
    
    # Function to convert HTML to PDF
    function Convert-HtmlToPdf {
        param([string]$HtmlPath, [string]$PdfPath)
        
        # Option 1: Try wkhtmltopdf (best quality for code)
        $wkhtmltopdf = $null
        
        # Check common installation paths
        $possiblePaths = @(
            "wkhtmltopdf",  # In PATH
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
                & $wkhtmltopdf --page-size A4 --margin-top 0.5in --margin-bottom 0.5in --margin-left 0.5in --margin-right 0.5in --enable-local-file-access --print-media-type "$HtmlPath" "$PdfPath"
                return $true
            } catch {
                Write-Host "    [WARN] wkhtmltopdf failed: $($_.Exception.Message)" -ForegroundColor Yellow
            }
        }
        
        # Option 2: Try Chrome/Edge headless
        $browsers = @("chrome", "msedge", "google-chrome")
        foreach ($browser in $browsers) {
            if (Get-Command $browser -ErrorAction SilentlyContinue) {
                try {
                    & $browser --headless --disable-gpu --run-all-compositor-stages-before-draw --print-to-pdf="$PdfPath" --print-to-pdf-no-header --virtual-time-budget=5000 "$HtmlPath"
                    if (Test-Path $PdfPath) {
                        return $true
                    }
                } catch {
                    Write-Host "    [WARN] $browser failed: $($_.Exception.Message)" -ForegroundColor Yellow
                }
            }
        }
        
        return $false
    }
    
    # Convert HTML to PDF
    if (Convert-HtmlToPdf -HtmlPath $HtmlFile -PdfPath $PdfFile) {
        Write-Host "  [SUCCESS] PDF created: $PdfFile" -ForegroundColor Green
    } else {
        Write-Host "  [WARN] PDF creation failed - install wkhtmltopdf or use Chrome/Edge" -ForegroundColor Yellow
        Write-Host "    Install wkhtmltopdf: https://wkhtmltopdf.org/downloads.html" -ForegroundColor Gray
    }
}

Write-Host ""
Write-Host "Opening HTML files..." -ForegroundColor Cyan

# Open all created HTML files
Get-ChildItem -Path $OutputDir -Filter "*_Documentation.html" | ForEach-Object {
    Start-Process $_.FullName
}

Write-Host ""
Write-Host "Documentation generation complete!" -ForegroundColor Green
Write-Host "Files created in: $OutputDir" -ForegroundColor White
Write-Host ""
Write-Host "Created files:" -ForegroundColor Gray
Get-ChildItem -Path $OutputDir | ForEach-Object {
    Write-Host "  $($_.Name)" -ForegroundColor Gray
}