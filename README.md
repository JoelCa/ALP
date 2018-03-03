# Proof assistant

Proof assistant of propositional second order logic, based
in coqtop.

## Setup

Download the proof assistan code at:

[Proof assistant](https://github.com/JoelCa/ALP/tree/master/proofAssistant)

In the root directory make:

```
$ stack setup
$ stack build
```

Then, for the execution:

```
$ cd app
$ stack exec proofAssistant
```

## Test examples

Load mannualy in the proof assistant.

* [example1.pr](https://github.com/JoelCa/ALP/blob/master/proofAssistant/app/example1.pr)
* [example2.pr](https://github.com/JoelCa/ALP/blob/master/proofAssistant/app/example2.pr)

## Dependencies

* Stack Version 1.5.1
* Cabal Version 2.0.0.0

