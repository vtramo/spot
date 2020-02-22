#!/bin/bash

if [ $# -ne 2 ]; then
    echo "Usage: ./run.sh DATA_DIRECTORY LOG_DIRECTORY"
    exit 1
fi

data_dir="$1"
log_dir="$2"
# Memory size samples
mem_sizes=$((10**6)),$((10**7)),$((10**8))

mkdir -p "$log_dir"

for model in $(find $data_dir -name "*.dve"); do
    model_name=$(basename "$model" .dve)
    log_file="$log_dir"/"$model_name".log.csv

    echo -n "Running model $model_name "
    ./bitstate "$model" "$log_file" "$mem_sizes" 2> /dev/null
    if [ $? -eq 0 ]; then
        echo -e "\e[1m\e[32mOK\e[0m"
    else
        echo -e "\e[1m\e[31mNOT OK\e[0m"
    fi
done
