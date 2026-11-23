module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.EtDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubsingletonH
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInFamily
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.AtlasOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CmpPutSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.EpsTA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CrSEqOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.InWmTeichmullerSubOne

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.CmpPutrNe

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Polynomial

universe w w' v u v' u'

namespace CrystallineSemistableComparison.HT.Rees

open CH B GlobalTheory.CompanionTheory.ReesDown

section
variable {R : Type} [CommRing R] {D : Type u} [Category.{v} D] {F : D ⥤ ModuleCat.{w} R} (Ψ : Flt F)

def putr (r j : ℕ) (z : Cn (Ψ.S r).fn j) : Cn Ψ.rees j := fun s =>
  show Ψ.Pr _ from Pi.single (M := fun r => (Ψ.S r).S (s.obj (Fin.last j))) r (z s)

theorem cmp_putr (r j : ℕ) (z : Cn (Ψ.S r).fn j) : cmp Ψ r j (putr Ψ r j z) = (Ψ.S r).inc.pullC j z :=
  funext fun s => congrArg Subtype.val (Pi.single_eq_same (M := fun r => (Ψ.S r).S (s.obj (Fin.last j))) r (z s))

theorem cmp_putr_ne {r r' : ℕ} (h : r' ≠ r) (j : ℕ) (z : Cn (Ψ.S r).fn j) : cmp Ψ r' j (putr Ψ r j z) = 0 :=
  funext fun s => congrArg Subtype.val (Pi.single_eq_of_ne (M := fun r => (Ψ.S r).S (s.obj (Fin.last j))) h (z s))

theorem putr_d (r j : ℕ) (z : Cn (Ψ.S r).fn j) : d Ψ.rees j (putr Ψ r j z) = putr Ψ r (j + 1) (d _ j z) := by
  refine cochain_ext Ψ fun r' => ?_
  rw [cmp_d]
  by_cases h : r' = r
  · subst h
    rw [cmp_putr, cmp_putr, Mor.d_pullC]
  · rw [cmp_putr_ne Ψ h, cmp_putr_ne Ψ h, map_zero]

theorem putr_zero (r j : ℕ) : putr Ψ r j 0 = 0 := by
  refine cochain_ext Ψ fun r' => ?_
  by_cases h : r' = r
  · subst h
    rw [cmp_putr, map_zero]; rfl
  · rw [cmp_putr_ne Ψ h]; rfl

theorem putr_mem_B (r j : ℕ) (a : Cn (Ψ.S r).fn j) (h : a ∈ (cx (Ψ.S r).fn).B j) : putr Ψ r j a ∈ (cx Ψ.rees).B j := by
  cases j with
  | zero =>
    have : a = 0 := h
    rw [this, putr_zero]
    exact Submodule.zero_mem _
  | succ j =>
    obtain ⟨e, rfl⟩ := h
    exact ⟨putr Ψ r j e, putr_d Ψ r j e⟩

theorem inc_inj (r j : ℕ) {a b : Cn (Ψ.S r).fn j} (h : (Ψ.S r).inc.pullC j a = (Ψ.S r).inc.pullC j b) : a = b :=
  funext fun s => Subtype.ext (congrFun h s)

theorem inc_cmpS (r j : ℕ) (f : Cn Ψ.rees j) : (Ψ.S r).inc.pullC j (cmpS Ψ r j f) = cmp Ψ r j f := rfl

theorem cmpS_d (r j : ℕ) (f : Cn Ψ.rees j) : cmpS Ψ r (j + 1) (d Ψ.rees j f) = d _ j (cmpS Ψ r j f) :=
  inc_inj Ψ r _ (by rw [inc_cmpS, cmp_d, ← Mor.d_pullC, inc_cmpS])

theorem cmpS_mem_B (r j : ℕ) (a : Cn Ψ.rees j) (h : a ∈ (cx Ψ.rees).B j) : cmpS Ψ r j a ∈ (cx (Ψ.S r).fn).B j := by
  cases j with
  | zero =>
    have : a = 0 := h
    rw [this]
    exact Submodule.zero_mem _
  | succ j =>
    obtain ⟨e, rfl⟩ := h
    exact ⟨cmpS Ψ r j e, (cmpS_d Ψ r j e).symm⟩

theorem cmp_X_pow' (j r k : ℕ) (f : Cn Ψ.rees j) : cmp Ψ (r + k) j ((X : ℤ[X]) ^ k • f) = Ψ.μ ^ k • cmp Ψ r j f := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_smul, ← add_assoc, cmp_X, ih, pow_succ', mul_smul]

end

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R}
  (Φ : Flt F) (G : C' ⥤ C) {n N : ℕ}

theorem inj (hRI : RI ((X : ℤ[X]) ^ N) n Φ.rees G) {j : ℕ} (hj : j ≤ n) (r : ℕ) (h) (x : H (Φ.S r).fn j)
    (hx : (Mor.restrict (Φ.S r).fn G).pull j x = 0) : (mulSub (Φ.μ ^ N) (Φ.S r) (Φ.S (r + N)) h).pull j x = 0 := by
  have hU : UpTo ((X : ℤ[X]) ^ N) ((Mor.restrict Φ.rees G).pull j) := hRI j hj
  obtain ⟨z, hz, rfl⟩ := (P.cls_surj (cx (Φ.S r).fn) j).1 x
  have hpd : d (G ⋙ (Φ.S r).fn) j ((Mor.restrict (Φ.S r).fn G).pullC j z) = 0 := by rw [Mor.d_pullC, hz, map_zero]
  have h2 : (Mor.restrict (Φ.S r).fn G).pullC j z ∈ (cx (G ⋙ (Φ.S r).fn)).B j :=
    ((P.cls_surj (cx (G ⋙ (Φ.S r).fn)) j).2.1 _ hpd).1 hx
  have hZ : d Φ.rees j (putr Φ r j z) = 0 := by
    rw [putr_d, hz]; exact putr_zero Φ r _
  have hZ' : d (G ⋙ Φ.rees) j ((Mor.restrict Φ.rees G).pullC j (putr Φ r j z)) = 0 := by
    rw [Mor.d_pullC, hZ, map_zero]
  have h3 : (Mor.restrict Φ.rees G).pull j ((cx Φ.rees).cls _ hZ) = 0 :=
    ((P.cls_surj (cx (G ⋙ Φ.rees)) j).2.1 _ hZ').2 (putr_mem_B (Φ.comap G) r j _ h2)
  have hXZ : d Φ.rees j ((X : ℤ[X]) ^ N • putr Φ r j z) = 0 := by
    rw [map_smul, hZ, smul_zero]
  have h4 := hU.1 _ h3
  rw [← (P.cls_surj (cx Φ.rees) j).2.2.2.2 _ _ hZ hXZ] at h4
  have h5 := cmpS_mem_B Φ (r + N) j _ (((P.cls_surj (cx Φ.rees) j).2.1 _ hXZ).1 h4)
  have e : cmpS Φ (r + N) j ((X : ℤ[X]) ^ N • putr Φ r j z) = (mulSub (Φ.μ ^ N) (Φ.S r) (Φ.S (r + N)) h).pullC j z :=
    inc_inj Φ _ _ (by rw [inc_cmpS, cmp_X_pow', cmp_putr]; rfl)
  rw [e] at h5
  have hμ : d _ j ((mulSub (Φ.μ ^ N) (Φ.S r) (Φ.S (r + N)) h).pullC j z) = 0 := by rw [Mor.d_pullC, hz, map_zero]
  exact ((P.cls_surj (cx (Φ.S (r + N)).fn) j).2.1 _ hμ).2 h5

theorem surj (h0 : ∀ T, (Φ.S 0).S T = ⊤) (hRI : RI ((X : ℤ[X]) ^ N) n Φ.rees G) {j : ℕ} (hj : j ≤ n) (h) (y : H (G ⋙ F) j) :
    ∃ x : H (Φ.S N).fn j, (Mor.restrict (Φ.S N).fn G).pull j x = (mulTo (Φ.μ ^ N) ((Φ.comap G).S N) h).pull j y := by
  have hU : UpTo ((X : ℤ[X]) ^ N) ((Mor.restrict Φ.rees G).pull j) := hRI j hj
  have h0' : ∀ T, ((Φ.comap G).S 0).S T = ⊤ := fun T => h0 (G.obj T)
  obtain ⟨w, hw, rfl⟩ := (P.cls_surj (cx (G ⋙ F)) j).1 y
  have hW : d (G ⋙ Φ.rees) j (put (Φ.comap G) h0' j w) = 0 := by
    refine (put_d (Φ.comap G) h0' j w).trans ?_
    rw [hw]; exact put_zero (Φ.comap G) h0' _
  obtain ⟨x', hx'⟩ := hU.2 ((cx (G ⋙ Φ.rees)).cls (show (cx (G ⋙ Φ.rees)).X j from put (Φ.comap G) h0' j w) hW)
  obtain ⟨Z, hZ, rfl⟩ := (P.cls_surj (cx Φ.rees) j).1 x'
  have hZ' : d (G ⋙ Φ.rees) j ((Mor.restrict Φ.rees G).pullC j Z) = 0 := by
    rw [Mor.d_pullC, hZ, map_zero]
  have hXW : d (G ⋙ Φ.rees) j ((X : ℤ[X]) ^ N • put (Φ.comap G) h0' j w) = 0 := by
    rw [map_smul, hW, smul_zero]
  have hx2 := (P.mapH_cls (Mor.restrict Φ.rees G).hom j Z hZ hZ').symm.trans hx'
  rw [← (P.cls_surj (cx (G ⋙ Φ.rees)) j).2.2.2.2 _ _ hW hXW] at hx2
  have hB := ((P.cls_surj (cx (G ⋙ Φ.rees)) j).2.2.1 _ _ hZ' hXW).1 hx2
  have hc := cmpS_mem_B (Φ.comap G) N j _ hB
  have e : ∀ A : Cn (Φ.comap G).rees j, A = (Mor.restrict Φ.rees G).pullC j Z →
      cmpS (Φ.comap G) N j (A - (X : ℤ[X]) ^ N • put (Φ.comap G) h0' j w) =
        (show Cn ((Φ.comap G).S N).fn j from (Mor.restrict (Φ.S N).fn G).pullC j (cmpS Φ N j Z)) -
          (mulTo (Φ.μ ^ N) ((Φ.comap G).S N) h).pullC j w := by
    intro A hA
    refine inc_inj (Φ.comap G) _ _ ?_
    rw [inc_cmpS, cmp_sub, cmp_X_pow, cmp_put_zero, hA]
    rfl
  have hc' := (e _ rfl) ▸ hc
  have h1 : d (G ⋙ (Φ.S N).fn) j ((Mor.restrict (Φ.S N).fn G).pullC j (cmpS Φ N j Z)) = 0 := by
    rw [Mor.d_pullC, d_cmpS Φ N j Z hZ, map_zero]
  have h2 : d _ j ((mulTo (Φ.μ ^ N) ((Φ.comap G).S N) h).pullC j w) = 0 := by rw [Mor.d_pullC, hw, map_zero]
  exact ⟨(cx (Φ.S N).fn).cls _ (d_cmpS Φ N j Z hZ), ((P.cls_surj (cx ((Φ.comap G).S N).fn) j).2.2.1 _ _ h1 h2).2 hc'⟩

def coef {F₁ : C ⥤ ModuleCat.{w} R} {F₂ : C' ⥤ ModuleCat.{w'} R} (m : Mor F₁ F₂ (RingHom.id R)) : Mor (m.G ⋙ F₁) F₂ (RingHom.id R) :=
  ⟨𝟭 _, m.τ, m.nat⟩

theorem coef_bij {F₁ : C ⥤ ModuleCat.{w} R} {F₂ : C' ⥤ ModuleCat.{w'} R} (m : Mor F₁ F₂ (RingHom.id R))
    (h : ∀ T, Function.Bijective (m.τ T)) (j : ℕ) : Function.Bijective ((coef m).pull j) := by
  have : (coef m).G.IsLeftAdjoint := inferInstanceAs (𝟭 C').IsLeftAdjoint
  exact CrystallineSemistableComparison.P.adj_mor (coef m) h j

theorem coef_res {F₁ : C ⥤ ModuleCat.{w} R} {F₂ : C' ⥤ ModuleCat.{w'} R} (m : Mor F₁ F₂ (RingHom.id R)) (j : ℕ) (x : H F₁ j) :
    m.pull j x = (coef m).pull j ((Mor.restrict F₁ m.G).pull j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

variable {F' : C' ⥤ ModuleCat.{w'} R} (m : Mor F F' (RingHom.id R)) (hm : ∀ T, Function.Bijective (m.τ T)) (S' : ℕ → SubF F')
  (hS : ∀ r T x, m.τ T x ∈ (S' r).S T → x ∈ (Φ.S r).S (m.G.obj T))

include hm hS in
theorem sub_bij (r : ℕ) (h) (T : C') : Function.Bijective ((subMor m (Φ.S r) (S' r) h).τ T) := by
  refine ⟨fun x y e => Subtype.ext ((hm T).1 (congrArg Subtype.val e)), fun y => ?_⟩
  obtain ⟨x, hx⟩ := (hm T).2 y.1
  exact ⟨⟨x, hS r T x (hx ▸ y.2)⟩, Subtype.ext hx⟩

theorem pow_mem (k r : ℕ) (T : C) (x : F.obj T) (hx : x ∈ (Φ.S r).S T) : Φ.μ ^ k • x ∈ (Φ.S (r + k)).S T := by
  induction k with
  | zero => simpa using hx
  | succ k ih => rw [pow_succ', mul_smul]; exact Φ.mul _ T _ ih

theorem key {t μ u : R} (ht : t = μ * u) (N : ℕ) {M : Type w} [AddCommGroup M] [Module R M] (a : M) : t ^ N • a = u ^ N • μ ^ N • a := by
  rw [smul_smul, ht, mul_pow, mul_comm]

include hm hS in
theorem inj' (hRI : RI ((X : ℤ[X]) ^ N) n Φ.rees m.G) {j : ℕ} (hj : j ≤ n) {t u : R} (ht : t = Φ.μ * u) (r : ℕ) (h h')
    (x : H (Φ.S r).fn j) (hx : (subMor m (Φ.S r) (S' r) h).pull j x = 0) :
    (mulSub (t ^ N) (Φ.S r) (Φ.S (r + N)) h').pull j x = 0 := by
  rw [coef_res] at hx
  have h1 := (coef_bij _ (sub_bij Φ m hm S' hS r h) j).1 (hx.trans (map_zero _).symm)
  have h2 := inj Φ m.G hRI hj r (pow_mem Φ N r) x h1
  have e : (mulSub (t ^ N) (Φ.S r) (Φ.S (r + N)) h').pull j x =
      u ^ N • (mulSub (Φ.μ ^ N) (Φ.S r) (Φ.S (r + N)) (pow_mem Φ N r)).pull j x := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
    exact key ht N (z.1 s).1
  rw [e, h2, smul_zero]

include hm in
theorem surj' (h0 : ∀ T, (Φ.S 0).S T = ⊤) (hRI : RI ((X : ℤ[X]) ^ N) n Φ.rees m.G) {j : ℕ} (hj : j ≤ n) {t u : R}
    (ht : t = Φ.μ * u) (h h') (y : H F' j) :
    ∃ x : H (Φ.S N).fn j, (subMor m (Φ.S N) (S' N) h).pull j x = (mulTo (t ^ N) (S' N) h').pull j y := by
  obtain ⟨y, rfl⟩ := (coef_bij m hm j).2 y
  have hp : ∀ (T : C') (x : (m.G ⋙ F).obj T), Φ.μ ^ N • x ∈ ((Φ.comap m.G).S N).S T := fun T x => by
    have := pow_mem Φ N 0 (m.G.obj T) x (by rw [h0]; trivial)
    rwa [zero_add] at this
  obtain ⟨x, hx⟩ := surj Φ m.G h0 hRI hj hp y
  refine ⟨u ^ N • x, ?_⟩
  rw [map_smul, coef_res]
  refine (congrArg (fun a => u ^ N • (coef (subMor m (Φ.S N) (S' N) h)).pull j a) hx).trans ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
  exact (congrArg (u ^ N • ·) (map_smul (m.τ _) (Φ.μ ^ N) (z.1 s))).trans (key ht N _).symm

end CrystallineSemistableComparison.HT.Rees
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.ReductionCommutesTMor

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris Formalism.Per6

universe w w' v u v' u'

namespace CrystallineSemistableComparison.HT.Red

open CH PAlg B

section Gen
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R}

theorem sub_mulSub (m : CH.Mor F F' (RingHom.id R)) (c : R) (S₁ S₂ : SubF F) (S₁' S₂' : SubF F') (h₁ h₂ k k') (j : ℕ) (x : H S₁.fn j) :
    (subMor m S₂ S₂' h₂).pull j ((mulSub c S₁ S₂ k).pull j x) = (mulSub c S₁' S₂' k').pull j ((subMor m S₁ S₁' h₁).pull j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext (map_smul (m.τ _) c _)))

theorem sub_mulTo (m : CH.Mor F F' (RingHom.id R)) (c : R) (S : SubF F) (S' : SubF F') (h k k') (j : ℕ) (x : H F j) :
    (subMor m S S' h).pull j ((mulTo c S k).pull j x) = (mulTo c S' k').pull j (m.pull j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext (map_smul (m.τ _) c _)))

theorem mulSub_mulTo (c c' c'' : R) (e : c'' = c' * c) (S S' : SubF F) (k k' k'') (j : ℕ) (x : H F j) :
    (mulSub c' S S' k').pull j ((mulTo c S k).pull j x) = (mulTo c'' S' k'').pull j x := by
  subst e
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext (mul_smul c' c _).symm))

end Gen

section Pd
variable {b b' : Base} {L : b.Fun} {L' : b'.Fun} {Λ : Type} [CommRing Λ] {c : Λ →+* b.R} {c' : Λ →+* b'.R} {σ : b.R →+* b'.R}

theorem om_sh (m : GlobalTheory.LogCris.Mor L L' σ) (h : ∀ a, σ (c a) = c' (RingHom.id Λ a)) {t : Λ} (ht : c t ∈ b.I) (ht' : c' t ∈ b'.I)
    {r r' : ℕ} (k : ℕ) (e : r + k = r') (j : ℕ) (x : H (pdS L c r).fn j) :
    (pdOm m (RingHom.id Λ) h r').pull j ((pdSh L c ht k e).pull j x) =
      (pdSh L' c' ht' k e).pull j ((pdOm m (RingHom.id Λ) h r).pull j x) :=
  sub_mulSub (omMor m (RingHom.id Λ) h) (t ^ k) _ _ _ _ _ _ _ _ j x

end Pd

section PdCr
variable {O : Type} [CommRing O] {F : Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}

theorem cr_pull_eq' {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c : Λ →+* b.R} {σ : Λ →+* Λ'} {C' : Type u} [Category.{v} C']
    {F' : C' ⥤ ModuleCat.{w} Λ'} (r : ℕ) (m m' : CH.Mor (pdS (F.cr b ht κ) c r).fn F' σ) (η : ∀ T, m.G.obj T ⟶ m'.G.obj T)
    (nat : ∀ {T T' : C'} (f : T ⟶ T') (x : (m.G.obj T).B), (η T').φ ((m.G.map f).φ x) = (m'.G.map f).φ ((η T).φ x))
    (hτ : ∀ (T : C') x, m'.τ T (((pdS (F.cr b ht κ) c r).fn.map (η T)).hom x) = m.τ T x) (n : ℕ) (x : H (pdS (F.cr b ht κ) c r).fn n) :
    m.pull n x = m'.pull n x :=
  CrystallineSemistableComparison.P.prism m m' ⟨η, fun _ _ f => Thick.Hom.ext (RingHom.ext (nat f)) (funext fun j => j.elim)⟩ hτ n x

end PdCr

theorem map_eq (P : CommRingCat.{0} ⥤ Type) {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) (h : A →+* C) (e : g.comp f = h) (y : P.obj (CommRingCat.of A)) :
    P.map (CommRingCat.ofHom g) (P.map (CommRingCat.ofHom f) y) = P.map (CommRingCat.ofHom h) y := by
  rw [← Functor.map_comp_apply, ← CommRingCat.ofHom_comp, e]

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

def redT (P : PAlg l ⥤ Type) (r n : ℕ) : CH.Mor (TT P r (n + 1)).fn (TT P r n).fn (RingHom.id _) :=
  subMor (CH.Mor.ofNatTrans (redEl P n.le_succ)) _ _ fun T x hx =>
    mem_TT.2 (Pb.dividedPowerFiltration_map (dd_red false T.1.obj n.le_succ) r (mem_TT.1 hx))

theorem reduction_commutes_tMor (ht : TFil l) (P : PAlg l ⥤ Type) (r n j : ℕ) (y : MH P (n + 1) j) :
    (redT P r n).pull j ((tMor ht P r (n + 1)).pull j y) = (tMor ht P r n).pull j ((MSys P j).r n y) :=
  sub_mulTo (CH.Mor.ofNatTrans (redEl P n.le_succ)) (tA l ^ r) _ _ _ _ _ j y

theorem red_uJ (k : Bool) (A : PAlg l) {m n : ℕ} (h : n ≤ m) (hle : JJ k A m ≤ (JJ k A n).comap (A.red h)) :
    (Ideal.quotientMap _ (A.red h) hle).comp (uJ k A m) = uJ k A n :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

theorem red_comm (A : PAlg l) {m n : ℕ} (h : n ≤ m) (r : (base l).Acr m) :
    A.red h (mapAcr A.fromBase m r) = mapAcr A.fromBase n ((base l).red h r) :=
  PdOk.red_acr (pdOk_hom A.fromBase) h r

def redTh (n : ℕ) (T : El (F.pt κ)) :
    (gT F κ false (n + 1)).obj T ⟶ (SH.redM F κ false n).functor.obj ((gT F κ false n).obj T) :=
  crHom (T := gObj F κ false (n + 1) ((jE _).obj T)) (T' := (SH.redM F κ false n).obj (gObj F κ false n ((jE _).obj T)))
    (T.1.obj.red n.le_succ) (red_comm T.1.obj n.le_succ) (dd_red false T.1.obj n.le_succ)
    fun h => map_eq F.Pt _ _ _ (red_uJ false T.1.obj n.le_succ h) T.2.1

theorem β_red (r n j : ℕ) (x : H (pdS (Lc F κ false (n + 1)) ((base l).cris (n + 1)) r).fn j) :
    (βMorF F κ r n).pull j ((pdOm (SH.redM F κ false n) (RingHom.id _) (red_cris _ n.le_succ) r).pull j x) =
      (redT (F.pt κ) r n).pull j ((βMorF F κ r (n + 1)).pull j x) :=
  ((pull_pull (RingHom.id _) (pdOm (SH.redM F κ false n) (RingHom.id _) (red_cris _ n.le_succ) r) (βMorF F κ r n) j x).trans
    (cr_pull_eq' r ((βMorF F κ r (n + 1)).comp (redT (F.pt κ) r n))
      ((pdOm (SH.redM F κ false n) (RingHom.id _) (red_cris _ n.le_succ) r).comp (βMorF F κ r n)) (redTh F κ n)
      (fun f x => PdOk.red_acr (pdOk_hom f.1.hom) n.le_succ x) (fun T x => rfl) j x).symm).trans
    (pull_pull (RingHom.id _) (βMorF F κ r (n + 1)) (redT (F.pt κ) r n) j x).symm

theorem tt_mul (ht : TFil l) (P : PAlg l ⥤ Type) {r r' : ℕ} (k : ℕ) (e : r + k = r') (n : ℕ) (T : El P)
    (x : (modF (AcrEl P n)).obj T) (hx : x ∈ (TT P r n).S T) : tA l ^ k • x ∈ (TT P r' n).S T := by
  have := dividedPowerFiltration_pow_mul (DD false T.1.obj n) (ht T.1.obj n) e (mem_TT.1 hx)
  rw [← map_pow] at this
  exact mem_TT.2 this

theorem β_sh (ht : TFil l) {r r' : ℕ} (k : ℕ) (e : r + k = r') (n j : ℕ) (x : H (pdS (Lc F κ false n) ((base l).cris n) r).fn j)
    (y : MH (F.pt κ) n j) (h : (βMorF F κ r n).pull j x = (tMor ht (F.pt κ) r n).pull j y) :
    (βMorF F κ r' n).pull j ((pdSh (Lc F κ false n) ((base l).cris n) (ht (base l) n) k e).pull j x) =
      (tMor ht (F.pt κ) r' n).pull j y :=
  (sub_mulSub (βMor F κ false n) (tA l ^ k) _ _ _ _ _ _ _ (tt_mul ht (F.pt κ) k e n) j x).trans
    ((congrArg ((mulSub (tA l ^ k) (TT (F.pt κ) r n) (TT (F.pt κ) r' n) (tt_mul ht (F.pt κ) k e n)).pull j) h).trans
      (mulSub_mulTo (tA l ^ r) (tA l ^ k) (tA l ^ r') (by rw [← e, add_comm, pow_add]) _ _ _ _ _ j y))

end CrystallineSemistableComparison.HT.Red
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.ExistsIsLiftOfEtP

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris Formalism.Per6

namespace CrystallineSemistableComparison.HT

open CH PAlg B

variable {l : ℕ} [Fact l.Prime]

namespace Ex

section Fn
variable {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ht : TFil l)

def Lvl (N j n : ℕ) : Prop :=
  (∀ (r : ℕ) (x : H (pdS (Lc F κ false n) ((base l).cris n) r).fn j), (βMorF F κ r n).pull j x = 0 →
    (pdSh (Lc F κ false n) ((base l).cris n) (ht (base l) n) N (rfl : r + N = r + N)).pull j x = 0) ∧
  ∀ y : MH (F.pt κ) n j, ∃ x, (βMorF F κ N n).pull j x = (tMor ht (F.pt κ) N n).pull j y

theorem sub_triv {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {G : C ⥤ ModuleCat.{0} R} (S : SubF G)
    (h : ∀ T, Subsingleton (G.obj T)) (j : ℕ) : Subsingleton (H S.fn j) :=
  subsingleton_H _ (fun T => ⟨fun x y => Subtype.ext ((h T).elim _ _)⟩) j

theorem pd_triv {b : Base} (L : b.Fun) {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (h : Subsingleton b.R) (r j : ℕ) :
    Subsingleton (H (pdS L c r).fn j) :=
  sub_triv _ (fun T => (show Subsingleton T.B from T.i.codomain_trivial)) j

theorem lvl_zero (N j : ℕ) : Lvl F κ ht N j 0 :=
  ⟨fun r _ _ => (pd_triv (Lc F κ false 0) ((base l).cris 0) (acr_zero (base l)) (r + N) j).elim _ _,
    fun _ => ⟨0, (sub_triv (TT (F.pt κ) N 0) (fun T => acr_zero T.1.obj) j).elim _ _⟩⟩

theorem back (n r : ℕ) (T : El (F.pt κ)) (x : (Oc F κ false n).obj ((βMor F κ false n).G.obj T))
    (hx : (βMor F κ false n).τ T x ∈ (TT (F.pt κ) r n).S T) :
    x ∈ (pdS (Lc F κ false n) ((base l).cris n) r).S ((βMor F κ false n).G.obj T) :=
  (mem_pdS (T := gObj F κ false n ((jE _).obj T))).2 (mem_TT.1 hx)

theorem lvl_pos (ε : Eps l) (u : Acris l) (hu : tA l = ε.μ * u) (N j n : ℕ)
    (h : RI ((Polynomial.X : Polynomial ℤ) ^ N) j (flt F κ ε false n id slow_id).rees (gT F κ false n)) : Lvl F κ ht N j n :=
  ⟨fun r x hx => Rees.inj' (flt F κ ε false n id slow_id) (βMor F κ false n) (fun _ => Function.bijective_id)
      (fun r => TT (F.pt κ) r n) (back F κ n) h le_rfl hu r _ _ x hx,
    fun y => Rees.surj' (flt F κ ε false n id slow_id) (βMor F κ false n) (fun _ => Function.bijective_id)
      (fun r => TT (F.pt κ) r n) (pdFlt_zero _ _ id slow_id _ _) h le_rfl hu _ _ y⟩

theorem lvl_all {d : ℕ} (𝒜 : F.Atlas d) (j : ℕ) : ∃ N, ∀ n, Lvl F κ ht N j n :=
  (global_of (local_of (D.out l)) d j).imp fun N hN n => (eps_tA l).elim fun ε h => h.elim fun u hu =>
    match n with
    | 0 => lvl_zero F κ ht N j
    | n + 1 => lvl_pos F κ ht ε u hu N j (n + 1) (hN F κ ε false (n + 1) id slow_id n.succ_ne_zero (Or.inl rfl) 𝒜)

theorem eq_of {N j n : ℕ} (h : Lvl F κ ht N j n) (r : ℕ) (x x' : H (pdS (Lc F κ false n) ((base l).cris n) r).fn j)
    (e : (βMorF F κ r n).pull j x = (βMorF F κ r n).pull j x') :
    (pdSh (Lc F κ false n) ((base l).cris n) (ht (base l) n) N (rfl : r + N = r + N)).pull j x =
      (pdSh (Lc F κ false n) ((base l).cris n) (ht (base l) n) N (rfl : r + N = r + N)).pull j x' :=
  sub_eq_zero.1 ((map_sub _ x x').symm.trans (h.1 r (x - x') ((map_sub _ x x').trans (sub_eq_zero.2 e))))

theorem fam_ex {N j : ℕ} (h : ∀ n, Lvl F κ ht N j n) (y : ∀ n, MH (F.pt κ) n j)
    (hy : ∀ n, (MSys (F.pt κ) j).r n (y (n + 1)) = y n) :
    ∃ x : ∀ n, H (pdS (Lc F κ false n) ((base l).cris n) (N + N)).fn j,
      (∀ n, (pdOm (SH.redM F κ false n) (RingHom.id _) (red_cris _ n.le_succ) (N + N)).pull j (x (n + 1)) = x n) ∧
      ∀ n, (βMorF F κ (N + N) n).pull j (x n) = (tMor ht (F.pt κ) (N + N) n).pull j (y n) :=
  (Classical.axiomOfChoice fun n => (h n).2 (y n)).elim fun x hx =>
    ⟨fun n => (pdSh (Lc F κ false n) ((base l).cris n) (ht (base l) n) N (rfl : N + N = N + N)).pull j (x n),
      fun n => (Red.om_sh (SH.redM F κ false n) (red_cris _ n.le_succ) (ht (base l) (n + 1)) (ht (base l) n) N rfl j (x (n + 1))).trans
        (eq_of F κ ht (h n) N _ _ ((Red.β_red F κ N n j (x (n + 1))).trans
          ((congrArg ((Red.redT (F.pt κ) N n).pull j) (hx (n + 1))).trans ((Red.reduction_commutes_tMor ht (F.pt κ) N n j (y (n + 1))).trans
            ((congrArg ((tMor ht (F.pt κ) N n).pull j) (hy n)).trans (hx n).symm))))),
      fun n => Red.β_sh F κ ht N rfl n j (x n) (y n) (hx n)⟩

end Fn

end Ex

variable {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (ht : TFil l) {e : E.EtFam l K}

theorem lvl_M {M : Model l K} (hM : M.Sm) (j : ℕ) : ∃ N, ∀ n, Ex.Lvl (schFn M.p) (okToOC l K) ht N j n :=
  (GlueB'.atlas_of hM).elim fun _ hA => Ex.lvl_all _ _ ht hA.some j

theorem exists_isLift_of_etP (he : EtP e) : ∀ M : Model l K, M.Sm → ∀ j, ∃ r, ∀ v : M.T j, ∃ x, IsLift ht e r v x := fun M hM j =>
  (lvl_M ht hM j).elim fun N hN => ⟨N + N, fun v =>
    Ex.fam_ex (schFn M.p) (okToOC l K) ht hN (fun n => e M n j (v.lev n))
      fun n => (he.good.red M n j _).trans (congrArg (e M n j) (v.2 n))⟩

theorem shS_eq_of_isLift : ∀ M : Model l K, M.Sm → ∀ j, ∃ k, ∀ (r : ℕ) (v : M.T j) (x x' : Fam M r j), IsLift ht e r v x →
    IsLift ht e r v x' → shS ht k rfl x = shS ht k rfl x' := fun M hM j =>
  (lvl_M ht hM j).imp fun N hN r v x x' hx hx' => funext fun n =>
    Ex.eq_of (schFn M.p) (okToOC l K) ht (hN n) r (x n) (x' n) ((hx.2 n).trans (hx'.2 n).symm)

end CrystallineSemistableComparison.HT
end
end
end
