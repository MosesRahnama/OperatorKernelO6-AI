#!/bin/bash
# OperatorKernelO6 Training Data Collection Script
# Creates a comprehensive dataset for fine-tuning a local AI model

echo "🔥 COLLECTING TRAINING DATA FOR OPERATORKERNELO6 AI 🔥"
echo "Creating a personalized AI mathematician..."

# Create training directory
mkdir -p ai_training_data/raw_data
mkdir -p ai_training_data/processed_data
mkdir -p ai_training_data/datasets

echo "📚 Collecting Lean source code..."
find . -name "*.lean" -type f | while read file; do
    echo "Processing: $file"
    echo "=== LEAN SOURCE: $file ===" >> ai_training_data/raw_data/lean_code.txt
    cat "$file" >> ai_training_data/raw_data/lean_code.txt
    echo -e "\n\n" >> ai_training_data/raw_data/lean_code.txt
done

echo "📖 Collecting documentation..."
find . -name "*.md" -type f | while read file; do
    echo "Processing: $file"
    echo "=== DOCUMENTATION: $file ===" >> ai_training_data/raw_data/documentation.txt
    cat "$file" >> ai_training_data/raw_data/documentation.txt
    echo -e "\n\n" >> ai_training_data/raw_data/documentation.txt
done

echo "📄 Collecting configuration files..."
find . -name "lakefile.lean" -o -name "*.json" -o -name "lean-toolchain" | while read file; do
    echo "Processing: $file"
    echo "=== CONFIG: $file ===" >> ai_training_data/raw_data/config.txt
    cat "$file" >> ai_training_data/raw_data/config.txt
    echo -e "\n\n" >> ai_training_data/raw_data/config.txt
done

echo "✅ Data collection complete!"
echo "📊 Training data saved in ai_training_data/"
