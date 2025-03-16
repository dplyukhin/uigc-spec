#!/bin/bash

# List of models for which to generate formatted Latex
MODELS=("FaultModel" "Dynamic" "Monitors" "Exile" "Shadows" "UndoLogs")
trap 'echo "Exiting."; exit 1' SIGINT

# Create the `tex` and `logs` directories if needed
if [ ! -d tex ]; then
    mkdir tex
    mkdir logs
fi

cd tex

for model in "${MODELS[@]}"; do
    echo -n "Formatting $model.tla... "
    # Generate formatted Latex
    cmd="java -cp ../tla2tools.jar tla2tex.TLA -latexCommand pdflatex ../spec/$model.tla > ../logs/$model-tex.log"
    if eval "$cmd"; then
        echo "Success."
    else
        echo "Errors detected! See logs/$model-tex.log for details."
    fi
done