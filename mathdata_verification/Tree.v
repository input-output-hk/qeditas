Require Export Docs.
Require Export DocHash.

Parameter ttree : Type. 
Parameter stree : Type. 

Parameter import_signatures: option hashval -> stree -> list hashval -> gsign -> list hashval -> option (gsign * list hashval).
      