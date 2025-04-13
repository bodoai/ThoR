Guten Morgen, Andreas, nach unserer Diskussion gestern zu Elab/Delab von „blockless“ habe ich das Ganze jetzt, glaube ich zumindest, besser verstanden.

Wir haben v.a. zwei Ziele:
- Z1: schönere Delaboration
- Z2: Benutzer können Alloy-Ausdrücke direkt hinschreiben (ohne Verwendung von Rel)

Dabei haben wir diese (Haupt-)Probleme:
- P1: Übersetzung von Alloy-Variablennamen (`a`, `model/a`) in Lean-Variablennamen (`model.vars.a`) und zurück.
- P2: Wir brauchen „Markierungen“, an die wir die Delab ranhängen können. (Z.B. genügt die „Markierung“ `HAdd.hAdd` nicht, da man ja gar nicht weiß, ob das im Kontext von ThoR ist oder nicht. Dir fallen da sicher noch bessere Beispiele ein.)

Nach meinem Verständnis lässt sich (P1) am besten und vermutlich auch nur mit einem Makro lösen, während wir für (P2) die ganze Information in induktive Datentypen packen sollten. Ich nenne das mal Expression-/Formula-Tree.

Beispiel:

```
-- Variablendefinition wie bisher
typeclass vars :=
	a : :: set univ
```

Benutzer schreibt hin `[alloy| a + a = a]`. Das wird dann übersetzt in `ThoR.Rel.eq (ThoR.Rel.add model.vars.a model.vars.a) model.vars.a` (Expression-/Formula-Tree). Die induktiven Datentypen dafür müssten erst noch in ThoR.Rel erzeugt werden.

Was wir gestern ja diskutiert hatten, waren andere Lösungen, z.B. `[alloy| a + a = a]` wird übersetzt in einen „Zweig“ aus dem AST und dann wenden wir `eval` darauf an. Ich habe nochmal darüber nachgedacht. So kann das vermutlich nicht funktionieren, da dieses eval ja wegen (P1) ein Makro sein müsste. Das hat aber den gravierenden Nachteil, dass ich ein solches eval-Makro in einem Lemma nicht mit `unfold` o.ä. auspacken kann. Deshalb müssen wir das in zwei Schritte (einen mit `eval` einen mit Makro) zerlegen.

Damit würde ich gerne das folgende Konzept zur Diskussion stellen:

*Elaboration für „blockless“*:
1. Schritt (im Prinzip wie bisher): konkrete Alloy-Syntax -> AST

Beispiel: `[alloy| a + a = a]` -> `formula.relationComarisonOperation.relCompareOp.eq (expr.binaryRelOperation binRelOp.union (expr.string "a") (expr.string "a")) (expr.string "a")`



2. Schritt (*neu*): AST -> Formula-/Expression-Tree:

Beispiel:
`formula.relationComarisonOperation.relCompareOp.eq (expr.binaryRelOperation binRelOp.union (expr.string "a") (expr.string "a")) (expr.string "a")` -> `(ThoR.Rel.eq (ThoR.Rel.add model.vars.a model.vars.a) model.vars.a).eval`

Ob das `eval` direkt in der Elab mit rangeschrieben wird oder durch eine Coercion automatisch dazukommt - da bin ich mir nicht sicher, welche Vor-/Nachteile das jeweils hat.

Auf jeden Fall haben wir mit der Form des Ergebnis des 2. Schritts nun folgende Vorteile:
V1: Das kann in Lemmata ausgepackt und verarbeitet werden. Genauso wie das jetzt schon mit `Quantification` funktioniert.
V2: Die Delaboration hat alle Markierungen, die sie braucht, um eindeutig delaborieren zu können. Z.B. würde man `eval` einfach "wegschmeißen" und aus `ThoR.Rel.add $x $y` würde man `$x + $y` machen.

Einziges Fragezeichen das verbleibt: Für die Umwandlung der Variablennamen muss die Delab auf den AST aus dem Kontext zugreifen können. Meine Hoffnung wäre, dass die Delab auch aus Unexpandern heraus auf diesen Kontext zugreifen kann.

Was meinst Du?