module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleCochainEvaluationLinear : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ},
    (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x,
      ev R (α + β) p s h U x = ev R α p s h U x + ev R β p s h U x ∧
      ev R (α - β) p s h U x = ev R α p s h U x - ev R β p s h U x ∧
      ev R (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧
      ∀ c : ℤ, ev R (c • α) p s h U x = c • ev R α p s h U x) ∧
    (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
      Sec.res g (ev R α p s h U x) = ev R α p s h V (x.res g)) ∧
    (∀ α β : Cochain ((chains R).obj E) I n,
      (∀ p s h U x, ev R α p s h U x = ev R β p s h U x) → α = β) ∧
    (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U),
      ev R ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev R α p s h U (x.map f)) ∧
    ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x,
      ev R (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev R α p s h U x)
