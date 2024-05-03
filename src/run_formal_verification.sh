#!/bin/bash

# Start
echo "Running Formal Verification..."

# Run autofire Formal Verification
echo "    - counter.v"
sby -f formal.sby counter
