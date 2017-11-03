# verification

Verification-related documentation and code for [pluto](https://github.com/go-pluto/pluto).


## Isabelle build

We use the interactive theorem prover Isabelle to show the correctness of pluto's core concept: the IMAP CmRDT. The formaliziation can be found in the corresponding theory files *.thy* in the Isabelle folder.

In order to create the proof document and the HTML overview, please navigate to the Isabelle folder of the repository and use:

`$isabelle build -D . -o browser_info -v IMAP`

*written with Isabelle 2017*

To use this library, please reference to the AFP as described in https://www.isa-afp.org/using.html
