#!/bin/bash

# Start
echo "Running Formal Verification..."

# Run autofire Formal Verification
echo "    - apu.v"
echo "        + module LenCounterUnit()"
sby -f formal.sby apu_LenCounterUnit
echo "        + module EnvelopeUnit()"
sby -f formal.sby apu_envelopeUnit
