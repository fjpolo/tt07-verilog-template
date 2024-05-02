<!---

This file is used to generate your project datasheet. Please fill in the information below and delete any unused
sections.

You can also include images in this folder and reference them in the markdown. Each image must be less than
512 kb in size, and the combined size of all images must be less than 1 MB.
-->

## How it works

`ui_in[0]` works as Chip Enable pin, active high. This enables an 8 bit counter that counts up to 128 and signals `uo_out[0]` for one clock cycle as active hhgh.

## How to test

Easy: count to 127, at clock 128 `uo_out[0]` should be 0. Clock once more, `uo_out[0]` should be 1. Count one cycle again, `uo_out[0]` should be 0.

## External hardware

`ui_in[0]` can be tied to HIGH.
`uo_out[0]` can be an LED