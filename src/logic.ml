open Hash

type stp =
| TpVar of int
| Base of int
| TpAll of stp
| TpArr of stp * stp
| Prop

type trm =
| DB of int
| TmH of hashval
| Prim of int
| Ap of trm * trm
| Lam of stp * trm
| Imp of trm * trm
| All of stp * trm
| TTpAp of trm * stp
| TTpLam of trm
| TTpAll of trm

type pf =
| Known of hashval
| Hyp of int
| PrAp of pf * pf
| TmAp of pf * trm
| TpAp of pf * stp
| PrLa of trm * pf
| TmLa of stp * pf
| TpLa of pf

type gsign = ((hashval * stp) * trm option) list * (hashval * trm) list

type theoryitem =
| Thyprim of stp
| Thyaxiom of trm
| Thydef of stp * trm

type theoryspec = theoryitem list

type theory = stp list * hashval list

type signaitem =
| Signasigna of hashval
| Signaparam of hashval * stp
| Signadef of stp * trm
| Signaknown of trm

type signaspec = signaitem list

type signa = hashval list * gsign

type docitem =
| Docsigna of hashval
| Docparam of hashval * stp
| Docdef of stp * trm
| Docknown of trm
| Docpfof of trm * pf
| Docconj of trm

type doc = docitem list
