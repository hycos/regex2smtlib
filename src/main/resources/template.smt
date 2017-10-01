{{#cvc4}}
(set-logic QF_S)
(set-option :produce-models true)
(set-option :strings-exp true)
(declare-fun {{vname}} () String)
{{/cvc4}}
{{#z3}}(declare-fun {{vname}} () String){{/z3}}
{{#z3str2}}(declare-const {{vname}} String){{/z3str2}}
{{<conjunct}}{{/conjunct}}
(check-sat)
(get-model)