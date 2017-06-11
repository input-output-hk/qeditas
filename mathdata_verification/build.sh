#!/bin/bash

rm *.vo *.glob .*.aux

coqc ListNth.v
coqc Hash.v
coqc Logic.v
coqc Checking.v
coqc Docs.v
coqc DocHash.v
coqc Tree.v
coqc MathData.v
coqc DocLogic.v
coqc TpVerif.v -R ./cpdt/src Cpdt
coqc TrmVerif.v -R ./cpdt/src Cpdt
coqc ProofVerif.v -R ./cpdt/src Cpdt
coqc ThyVerif.v -R ./cpdt/src Cpdt
coqc SgnVerif.v -R ./cpdt/src Cpdt
coqc DocVerif.v -R ./cpdt/src Cpdt
coqc Extractions.v
