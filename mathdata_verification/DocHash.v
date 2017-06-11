Require Export Docs.

Parameter hash_stp : stp -> hashval.

Parameter hash_trm : trm -> hashval.
Parameter trm_hashroot : trm -> hashval.

Parameter hash_pf : pf -> hashval .
Parameter pf_hashroot : pf -> hashval.

Parameter hash_theoryitem : theoryitem -> hashval.
Parameter hash_theory : theory -> hashval.
Parameter hash_theoryspec : theoryspec -> hashval.

Parameter theoryspec_hashroot : theoryspec -> hashval.
Parameter hash_signaitem : signaitem -> hashval.
Parameter hash_signaspec : signaspec -> hashval.
Parameter signaspec_hashroot : signaspec -> hashval.
Parameter hash_gsign : gsign -> hashval.
Parameter hash_signa : signa -> hashval.

Parameter hash_docitem : docitem -> hashval.
Parameter hash_doc : doc -> hashval.
Parameter docitem_hashroot : docitem -> hashval.
Parameter doc_hashroot : doc -> hashval.
Parameter pdoc_hashroot : pdoc -> hashval.
