module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemEigSp
public import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyFamilyUnifIffUnifAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDerivAt0CompLinearIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpDerEigenIff

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.UPel.HT.LieType

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {g : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)}

def expDer (he : IsExp y e) (w : Fin g → ℂ) : epsPt y ⟶ G := (he.2.2.2.1 w).exists.choose

variable (he : IsExp y e)
include he

theorem expDer_spec (w : Fin g → ℂ) : IsDerivAt0 (fun z => (e z).left) w (expDer he w).left :=
  (he.2.2.2.1 w).exists.choose_spec

theorem exp_zero : e 0 = 1 := by
  have h := he.1 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem expDer_eq_iff (w : Fin g → ℂ) (v : epsPt y ⟶ G) :
    IsDerivAt0 (fun z => (e z).left) w v.left ↔ expDer he w = v :=
  ⟨fun hv => Over.OverMorphism.ext
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique (expDer_spec he w) hv), fun hv => hv ▸ expDer_spec he w⟩

theorem expDer_base (w : Fin g → ℂ) :
    spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (expDer he w).left = (1 : Over.mk y ⟶ G).left := by
  rw [(expDer_spec he w).1]; show (e 0).left = _; rw [exp_zero he]

theorem expDer_injective : Function.Injective (expDer he) := by
  intro w w' h
  have h1 := expDer_spec he w
  have h2 := expDer_spec he w'
  rw [← h] at h2
  have hb : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (expDer he w).left = (e 0).left := h1.1
  exact (he.2.2.2.2 _ hb).unique h1 h2

theorem expDer_surj (v : epsPt y ⟶ G)
    (hv : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (1 : Over.mk y ⟶ G).left) :
    ∃ w, expDer he w = v := by
  obtain ⟨w, hw, -⟩ := he.2.2.2.2 v (by rw [hv, exp_zero he])
  exact ⟨w, (expDer_eq_iff he w v).1 hw⟩

theorem expDer_add (w w' : Fin g → ℂ) : expDer he (w + w') = expDer he w * expDer he w' :=
  (expDer_eq_iff he _ _).1 (GlobalTheory.UnifCompare.isDerivAt0_mul (by rw [exp_zero he]) (expDer_spec he w)
    (expDer_spec he w'))

theorem expDer_zero : expDer he 0 = 1 := by
  have h := expDer_add he 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem expDer_smul (c : ℂ) (w : Fin g → ℂ) :
    (expDer he (c • w)).left = spMap (epsScale c) ≫ (expDer he w).left :=
  ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique (expDer_spec he _)
    (GlobalTheory.UnifCompare.isDerivAt0_smul (expDer_spec he w) c)

theorem expDer_prod {n : ℕ} (f : Fin n → Fin g → ℂ) :
    (List.ofFn fun j => expDer he (f j)).prod = expDer he (∑ j, f j) := by
  induction n with
  | zero => simp [expDer_zero he]
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, ih (fun j => f j.succ), Fin.sum_univ_succ, expDer_add he]

theorem expDer_mulVec (M : Matrix (Fin g) (Fin g) ℂ) (φ : G ⟶ G) (hM : ∀ z, e (M *ᵥ z) = e z ≫ φ)
    (w : Fin g → ℂ) : expDer he (M *ᵥ w) = expDer he w ≫ φ := by
  have h1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_comp_hom (expDer_spec he w) φ.left
  have h2 : (fun z => (e z).left ≫ φ.left) = fun z => (e (Matrix.mulVecLin M z)).left := by
    funext z; rw [Matrix.mulVecLin_apply, hM z, Over.comp_left]
  rw [h2, GlobalTheory.ThetaWitness.isDerivAt0_comp_linear_iff (fun z => (e z).left) he.2.2.1] at h1
  exact (expDer_eq_iff he _ _).1 h1

theorem expDer_eigen_iff (M : Matrix (Fin g) (Fin g) ℂ) (φ : G ⟶ G) (hM : ∀ z, e (M *ᵥ z) = e z ≫ φ)
    (c : ℂ) (w : Fin g → ℂ) :
    (expDer he w ≫ φ).left = spMap (epsScale c) ≫ (expDer he w).left ↔ M *ᵥ w = c • w := by
  rw [← expDer_mulVec he M φ hM, ← expDer_smul he]
  constructor
  · intro h
    exact expDer_injective he (Over.OverMorphism.ext h)
  · intro h
    rw [h]

end GlobalTheory.UPel.HT.LieType
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieTypeOfUnif

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType

noncomputable section

namespace GlobalTheory.LieEigenspaceFinrank

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {g : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)}

theorem isLieEigen_iff (he : IsExp y e) {F : Type} [Field F] [NumberField F]
    (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (act : OAct (𝓞 F) G)
    (hM : ∀ c z, e (φ c *ᵥ z) = e z ≫ act.act c) (τ : F →+* ℂ) (τ' : 𝓞 F →+* ℂ)
    (hτ : ∀ c : 𝓞 F, τ (c : F) = τ' c) (w : Fin g → ℂ) :
    IsLieEigen act y τ' (expDer he w) ↔ w ∈ eigSp φ τ := by
  rw [mem_eigSp]
  constructor
  · intro h c
    rw [hτ]
    exact (expDer_eigen_iff he (φ c) (act.act c) (hM c) (τ' c) w).1 (h.2 c)
  · intro h
    refine ⟨expDer_base he w, fun c => ?_⟩
    exact (expDer_eigen_iff he (φ c) (act.act c) (hM c) (τ' c) w).2 (by rw [← hτ]; exact h c)

theorem comb_iff (he : IsExp y e) {n : ℕ} (w : Fin n → Fin g → ℂ) (c : Fin n → ℂ) (z : Fin g → ℂ) :
    (∃ u : Fin n → (epsPt y ⟶ G), (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (expDer he (w i)).left) ∧
      expDer he z = (List.ofFn u).prod) ↔ z = ∑ i, c i • w i := by
  constructor
  · rintro ⟨u, hu, hz⟩
    have hu' : u = fun i => expDer he (c i • w i) := by
      funext i
      exact Over.OverMorphism.ext (by rw [hu i, expDer_smul he])
    rw [hu', expDer_prod he (fun i => c i • w i)] at hz
    exact expDer_injective he hz
  · intro hz
    refine ⟨fun i => expDer he (c i • w i), fun i => expDer_smul he _ _, ?_⟩
    rw [expDer_prod he (fun i => c i • w i), hz]

theorem finrank_eigSp (he : IsExp y e) {F : Type} [Field F] [NumberField F]
    (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (act : OAct (𝓞 F) G)
    (hM : ∀ c z, e (φ c *ᵥ z) = e z ≫ act.act c) (τ : F →+* ℂ) (τ' : 𝓞 F →+* ℂ)
    (hτ : ∀ c : 𝓞 F, τ (c : F) = τ' c) (n : ℕ) (h : LieMult act y τ' n) :
    Module.finrank ℂ (eigSp φ τ) = n := by
  obtain ⟨v, hv, hb⟩ := h
  choose w hw using fun i => expDer_surj he (v i) (hv i).1
  obtain rfl : v = fun i => expDer he (w i) := funext fun i => (hw i).symm
  have hwm : ∀ i, w i ∈ eigSp φ τ := fun i => (isLieEigen_iff he φ act hM τ τ' hτ _).1 (hv i)
  have key : ∀ z ∈ eigSp φ τ, ∃! c : Fin n → ℂ, z = ∑ i, c i • w i := by
    intro z hz
    have := hb _ ((isLieEigen_iff he φ act hM τ τ' hτ z).2 hz)
    simpa only [comb_iff he w] using this
  let L : (Fin n → ℂ) →ₗ[ℂ] eigSp φ τ := Fintype.linearCombination ℂ (fun i => (⟨w i, hwm i⟩ : eigSp φ τ))
  have hL : ∀ c, (L c : Fin g → ℂ) = ∑ i, c i • w i := by
    intro c
    simp [L, Fintype.linearCombination_apply]
  have hbij : Function.Bijective L := by
    rw [Function.bijective_iff_existsUnique]
    intro z
    obtain ⟨c, hc, hu⟩ := key z.1 z.2
    refine ⟨c, Subtype.ext (by rw [hL]; exact hc.symm), fun c' hc' => hu c' ?_⟩
    exact (congrArg Subtype.val hc').symm.trans (hL c')
  rw [← (LinearEquiv.ofBijective L hbij).finrank_eq]
  simp

theorem lie_type_of_unif (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ))
    (h : SmoothOfRelativeDimension D.g o.A.hom) (hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB)
    (D' : PLat D.O D.inv) (t : D.La → D'.La) (Q : D'.La →+ (Fin D.g → ℂ))
    (e : (Fin D.g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ (o.fam h hL).A))
    (hU : UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 (Sp ℂ)) e) (τ : Fin D.a → D.F →+* ℂ)
    (hτ : ∀ (i : Fin D.a) (c : 𝓞 D.F), τ i (c : D.F) = σ (b.t i c)) :
    (∀ i, Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i)) = D.m) ∧
      ∀ u : Fin D.g → ℂ, ρ (algebraMap (𝓞 D.F) D.O D.ω) *ᵥ u = σ b.ρ • u →
        u ∈ ⨆ i, eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i) := by
  have he : IsExp (G := o.A) (𝟙 (Sp ℂ)) e := hU.2.2.1
  have hM : ∀ (a : D.O) z, e (ρ a *ᵥ z) = e z ≫ o.act.act a := hU.2.2.2.2.1
  have hx : 𝟙 (Sp ℂ) ≫ spMap σ = spMap σ := Category.id_comp _
  have hM' : ∀ (c : 𝓞 D.F) z, e ((ρ.comp (algebraMap (𝓞 D.F) D.O)) c *ᵥ z) = e z ≫ (o.act.toF D).act c :=
    fun c z => hM _ z
  refine ⟨fun i => ?_, fun u hu => ?_⟩
  · exact finrank_eigSp (G := o.A) he _ (o.act.toF D) hM' (τ i) (σ.comp (b.t i)) (hτ i) _
      (o.lieRank ℂ (𝟙 _) σ hx i)
  · obtain ⟨v, hv, hprod⟩ := o.lie ℂ σ (𝟙 _) hx (expDer (G := o.A) he u)
      ⟨expDer_base he u, (expDer_eigen_iff (G := o.A) he _ _ (hM _) (σ b.ρ) u).2 hu⟩
    choose w hw using fun i => expDer_surj (G := o.A) he (v i) (hv i 0).1
    obtain rfl : v = fun i => expDer (G := o.A) he (w i) := funext fun i => (hw i).symm
    have hu' : u = ∑ i, w i := expDer_injective he (hprod.trans (expDer_prod he w))
    rw [hu']
    refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ?_
    exact (isLieEigen_iff (G := o.A) he _ (o.act.toF D) hM' (τ i) (σ.comp (b.t i)) (hτ i) _).1
      ⟨(hv i 0).1, fun c => (hv i c).2⟩

end GlobalTheory.LieEigenspaceFinrank
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenspaceDimensionOfUniformization

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.UPel.HT.LieType

open GlobalTheory.UPel.HT

theorem lieEigen_rank_cover : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL (D' : PLat D.O D.inv) t Q e,
    UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → ∀ τ : Fin D.a → (D.F →+* ℂ),
    (∀ i (c : 𝓞 D.F), τ i (c : D.F) = σ (b.t i c)) →
    (∀ i, Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i)) = D.m) ∧
    ∀ u : Fin D.g → ℂ, ρ (algebraMap (𝓞 D.F) D.O D.ω) *ᵥ u = σ b.ρ • u →
      u ∈ ⨆ i, eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i) := by
  first
  | exact @_root_.GlobalTheory.LieEigenspaceFinrank.lie_type_of_unif
  | exact _root_.GlobalTheory.LieEigenspaceFinrank.lie_type_of_unif
  | (apply _root_.GlobalTheory.LieEigenspaceFinrank.lie_type_of_unif <;> assumption)
  | (intros; apply _root_.GlobalTheory.LieEigenspaceFinrank.lie_type_of_unif <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LieEigenspaceFinrank.lie_type_of_unif <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LieEigenspaceFinrank.lie_type_of_unif ..)

end GlobalTheory.UPel.HT.LieType
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenspaceDimensionOfUniformizationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType

theorem _root_.GlobalTheory.T.eigenspace_dimension_of_uniformization : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL (D' : PLat D.O D.inv) t Q e, UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → ∀ τ : Fin D.a → (D.F →+* ℂ), (∀ i (c : 𝓞 D.F), τ i (c : D.F) = σ (b.t i c)) → (∀ i, Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i)) = D.m) ∧ ∀ u : Fin D.g → ℂ, ρ (algebraMap (𝓞 D.F) D.O D.ω) *ᵥ u = σ b.ρ • u → u ∈ ⨆ i, eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i) := by
  first | exact @GlobalTheory.UPel.HT.LieType.lieEigen_rank_cover | exact GlobalTheory.UPel.HT.LieType.lieEigen_rank_cover | (intros; apply GlobalTheory.UPel.HT.LieType.lieEigen_rank_cover <;> assumption)
end
end
