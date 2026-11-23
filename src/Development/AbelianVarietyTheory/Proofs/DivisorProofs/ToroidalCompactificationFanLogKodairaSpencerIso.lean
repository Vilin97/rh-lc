module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidBoundaryChartsForFanUnitaryDatumStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerRegularFramedAffineStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizedModuleRes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerInjectiveModMaximalIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidChartDualNumberDeformation
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricBalancedTensorsFiniteProjectiveRankDim
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveOfInjectiveModMaximal

section

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory.ProjBij

theorem eq_bot_of_forall_le_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (K : Submodule R M) (hK : K.FG) (h : ∀ m : Ideal R, m.IsMaximal → K ≤ m • K) : K = ⊥ := by
  rw [← Submodule.annihilator_eq_top_iff]
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨r, hr, hr0⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m K hK (h m hm)
  have h1 : r ∈ m := hle (Submodule.mem_annihilator.2 hr0)
  apply hm.ne_top
  rw [Ideal.eq_top_iff_one]
  have := m.sub_mem h1 hr
  simpa using this

theorem one_tmul_eq_zero_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (m : Ideal R) (x : M) :
    ((1 : R ⧸ m) ⊗ₜ[R] x : (R ⧸ m) ⊗[R] M) = 0 ↔ x ∈ m • (⊤ : Submodule R M) := by
  rw [← (TensorProduct.quotTensorEquivQuotSMul M m).map_eq_zero_iff,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]

theorem exists_one_tmul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (m : Ideal R) (y : (R ⧸ m) ⊗[R] M) : ∃ x : M, (1 : R ⧸ m) ⊗ₜ[R] x = y :=
  TensorProduct.mk_surjective R M (R ⧸ m) Ideal.Quotient.mk_surjective y

theorem bijective_of_injective_mod_maximal
    (R M N : Type) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M] [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N)
    (hrk : ∀ m : Ideal R, m.IsMaximal →
      Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] M) = Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] N))
    (hinj : ∀ m : Ideal R, m.IsMaximal → ∀ x, f x ∈ m • (⊤ : Submodule R N) →
      x ∈ m • (⊤ : Submodule R M)) :
    Function.Bijective f := by
  have hsurj : Function.Surjective f := by
    have key : (⊤ : Submodule R (N ⧸ LinearMap.range f)) = ⊥ := by
      apply eq_bot_of_forall_le_smul _ Module.Finite.fg_top
      intro m hm y _
      letI := Ideal.Quotient.field m
      have hi : Function.Injective (f.baseChange (R ⧸ m)) := by
        set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
        intro z hz
        obtain ⟨x, rfl⟩ := exists_one_tmul m z
        rw [LinearMap.baseChange_tmul, one_tmul_eq_zero_iff] at hz
        exact (one_tmul_eq_zero_iff m x).2 (hinj m hm x hz)
      have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hrk m hm)).1 hi
      obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨z, hz⟩ := hs (1 ⊗ₜ n)
      obtain ⟨x, rfl⟩ := exists_one_tmul m z
      rw [LinearMap.baseChange_tmul, ← sub_eq_zero, ← TensorProduct.tmul_sub,
        one_tmul_eq_zero_iff] at hz
      have h2 := Submodule.mem_map_of_mem (f := (LinearMap.range f).mkQ) hz
      rw [Submodule.map_smul''] at h2
      have h3 := Submodule.smul_mono (le_refl m) le_top h2
      have h4 : (LinearMap.range f).mkQ (f x) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self f x)
      rw [map_sub, h4, zero_sub] at h3
      exact (Submodule.neg_mem_iff _).1 h3
    intro n
    have : (Submodule.Quotient.mk n : N ⧸ LinearMap.range f) ∈ (⊥ : Submodule R _) := by
      rw [← key]; trivial
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at this
    exact this
  refine ⟨?_, hsurj⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hsurj
  have hs' : ∀ n, f (s n) = n := fun n => LinearMap.congr_fun hs n
  let p : M →ₗ[R] M := LinearMap.id - s ∘ₗ f
  have hp : Submodule.map p ⊤ = LinearMap.ker f := by
    apply le_antisymm
    · rintro _ ⟨x, -, rfl⟩
      simp [p, hs']
    · intro x hx
      exact ⟨x, trivial, by simp [p, LinearMap.mem_ker.1 hx]⟩
  rw [← LinearMap.ker_eq_bot]
  apply eq_bot_of_forall_le_smul
  · rw [← hp]; exact Module.Finite.fg_top.map p
  · intro m hm x hx
    have hx0 : f x = 0 := hx
    have h1 := hinj m hm x (by rw [hx0]; exact Submodule.zero_mem _)
    have h2 := Submodule.mem_map_of_mem (f := p) h1
    rw [Submodule.map_smul'', hp] at h2
    simpa [p, hx0] using h2

end GlobalTheory.ProjBij
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricBalancedTensorsFiniteProjectiveRankDimStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.symmetric_balanced_tensors_finite_projective_rank_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → Module.Finite Γ(Y.X, U.1) (balanced H.bar A) ∧ Module.Projective Γ(Y.X, U.1) (balanced H.bar A) ∧ ∀ m : Ideal Γ(Y.X, U.1), m.IsMaximal → Module.finrank (Γ(Y.X, U.1) ⧸ m) ((Γ(Y.X, U.1) ⧸ m) ⊗[Γ(Y.X, U.1)] (balanced H.bar A)) = Dw.dim := by
  first | exact @GlobalTheory.BalProj.balanced_finite_projective_rank | exact GlobalTheory.BalProj.balanced_finite_projective_rank | (intros; apply GlobalTheory.BalProj.balanced_finite_projective_rank <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerIsoSmoothSncToroidalModel

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LogKSAssembly

theorem entry_mem_of_mem_smul_top {R : Type} [CommRing R] {n : ℕ} (N : Submodule R (Matrix (Fin n) (Fin n) R))
    (m : Ideal R) (y : N) (hy : y ∈ m • (⊤ : Submodule R N)) (a b : Fin n) : (y : Matrix (Fin n) (Fin n) R) a b ∈ m := by
  refine Submodule.smul_induction_on (p := fun y : N => (y : Matrix (Fin n) (Fin n) R) a b ∈ m) hy ?_ ?_
  · intro r hr x _
    simpa using m.mul_mem_right _ hr
  · intro x y hx hy
    simpa using m.add_mem hx hy

theorem exists_equiv {R L : Type} [CommRing R] [AddCommGroup L] [Module R L] [Module.Finite R L] [Module.Projective R L]
    {n : ℕ} (N : Submodule R (Matrix (Fin n) (Fin n) R)) [Module.Finite R N] [Module.Projective R N]
    (K : L → Matrix (Fin n) (Fin n) R → Prop) (hex : ∀ D, ∃ Θ, K D Θ) (huniq : ∀ D Θ Θ', K D Θ → K D Θ' → Θ = Θ')
    (hlin : ∀ D D' (r : R) Θ Θ', K D Θ → K D' Θ' → K (D + D') (Θ + Θ') ∧ K (r • D) (r • Θ))
    (hN : ∀ D Θ, K D Θ → Θ ∈ N)
    (hrk : ∀ m : Ideal R, m.IsMaximal →
      Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] L) = Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] N))
    (hfib : ∀ D Θ (m : Ideal R), m.IsMaximal → K D Θ → (∀ a b, Θ a b ∈ m) → D ∈ m • (⊤ : Submodule R L)) :
    ∃ e : L ≃ₗ[R] N, ∀ D Θ, K D Θ ↔ Θ = (e D).1 := by
  classical
  choose Θ hΘ using hex
  let f : L →ₗ[R] N :=
    { toFun := fun D => ⟨Θ D, hN D _ (hΘ D)⟩
      map_add' := fun D D' => Subtype.ext (huniq _ _ _ (hΘ (D + D')) (hlin D D' 1 _ _ (hΘ D) (hΘ D')).1)
      map_smul' := fun r D => Subtype.ext (huniq _ _ _ (hΘ (r • D)) (hlin D D r _ _ (hΘ D) (hΘ D)).2) }
  have hf : Function.Bijective f :=
    GlobalTheory.ProjBij.bijective_of_injective_mod_maximal R L N f hrk
      (fun m hm x hx => hfib x (Θ x) m hm (hΘ x) (entry_mem_of_mem_smul_top N m (f x) hx))
  refine ⟨LinearEquiv.ofBijective f hf, fun D Θ' => ⟨fun h => huniq D Θ' (Θ D) h (hΘ D), fun h => ?_⟩⟩
  rw [h]
  exact hΘ D



theorem hasLogKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → HasLogKS Y.t Y.s (interior Y) := by
  intro E _ _ _ H Dw l Xo c Y hr hsm hsnc hrig
  unfold HasLogKS
  intro U n v A hv hb hA
  obtain ⟨hLf, hLp, hLr⟩ := GlobalTheory.LogDerProj.main E H Dw l Xo c Y hr hsm hsnc U
  obtain ⟨hBf, hBp, hBr⟩ := GlobalTheory.T.symmetric_balanced_tensors_finite_projective_rank_dim E H Dw l Xo c Y hr hsm hsnc U n v A hv hb hA
  exact exists_equiv (balanced H.bar A) (fun D Θ => IsKS Y.t (interior Y) U v D.1 Θ)
    (GlobalTheory.T.exists_kodairaSpencer_regular_framed_affine E H Dw l Xo c Y hr hsm hsnc hrig U n v A hv hb hA)
    (GlobalTheory.KSUniq.isKS_unique_model E H Dw l Xo c Y hr hsm hsnc hrig U n v A hv hb hA)
    (GlobalTheory.LogKSLin.isKS_linear E H Dw l Xo c Y U n v A hv hb hA)
    (GlobalTheory.LogKSBal.ksClass_mem_balanced E H Dw l Xo c Y hr hsm hsnc hrig U n v A hv hb hA)
    (fun m hm => (hLr m hm).trans (hBr m hm).symm)
    (GlobalTheory.T.logKodairaSpencer_injective_mod_maximalIdeal E H Dw l Xo c Y hr hsm hsnc hrig U n v A hv hb hA)

end GlobalTheory.LogKSAssembly
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerIsoSmoothSncToroidalModelStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.logKodairaSpencer_iso_smooth_snc_toroidalModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → HasLogKS Y.t Y.s (interior Y) := by
  first | exact @GlobalTheory.LogKSAssembly.hasLogKS | exact GlobalTheory.LogKSAssembly.hasLogKS | (intros; apply GlobalTheory.LogKSAssembly.hasLogKS <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFanKodairaSpencerOfRigidBoundaryCharts

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.RigChart.toroidalForFanKS_of_rigidForFan : GlobalTheory.RigChart.RigidForFan → GlobalTheory.Published.ToroidalForFanKS := by
  intro h E _ _ _ H Dw hr φ h₁ h₂ l Xo c
  obtain ⟨Y, BD, d, k, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := h E H Dw hr φ h₁ h₂ l Xo c
  exact ⟨Y, BD, d, k, a₁, a₂, a₃, a₄, a₅, a₆, a₇, GlobalTheory.T.logKodairaSpencer_iso_smooth_snc_toroidalModel E H Dw l Xo c Y hr a₃ a₄ a₈⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFanKodairaSpencerOfRigidBoundaryChartsStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.toroidalFanKodairaSpencer_of_rigidBoundaryCharts : GlobalTheory.RigChart.RigidForFan → GlobalTheory.Published.ToroidalForFanKS := by
  first | exact @GlobalTheory.RigChart.toroidalForFanKS_of_rigidForFan | exact GlobalTheory.RigChart.toroidalForFanKS_of_rigidForFan | (intros; apply GlobalTheory.RigChart.toroidalForFanKS_of_rigidForFan <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalCompactificationFanLogKodairaSpencerIso

section

@[expose] public section

namespace GlobalTheory.TorKSField

theorem toroidalForFanKS : GlobalTheory.Published.ToroidalForFanKS :=
  GlobalTheory.T.toroidalFanKodairaSpencer_of_rigidBoundaryCharts GlobalTheory.T.rigidBoundaryChartsForFan_unitaryDatum

end GlobalTheory.TorKSField
end
end
