module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicBoxesCompactExhaustStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsRealFlowAdelicUnitsStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FundamentalDomainTransportCongruentFormStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicFiniteVolumeIntegralBoundStatement
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IsotropicVectorSplitsHyperbolicPlane

section

@[expose] public section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HypSplit

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem hE_eq_dot (u v : Fin M → E) :
    hE σ J u v = Matrix.vecMul (fun i => σ (u i)) J ⬝ᵥ v := by
  simp only [hE, hform, Matrix.vecMul, dotProduct, Finset.sum_mul, RingHom.coe_coe]
  exact Finset.sum_comm

def hLin (u : Fin M → E) : (Fin M → E) →ₗ[E] E where
  toFun := hE σ J u
  map_add' v w := by simp only [hE_eq_dot, dotProduct_add]
  map_smul' a v := by simp only [hE_eq_dot, dotProduct_smul, RingHom.id_apply]

@[simp] theorem hLin_apply (u v : Fin M → E) : hLin σ J u v = hE σ J u v := rfl

variable {σ J}

theorem hE_conj (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (u v : Fin M → E) :
    σ (hE σ J u v) = hE σ J v u := by

  simp only [hE, hform, map_sum, map_mul, RingHom.coe_coe, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

theorem exists_partner (hσ : ∀ a, σ (σ a) = a) (hJ : IsHermND σ J) (h2 : (2 : E) ≠ 0)
    (x : Fin M → E) (hx : x ≠ 0) (hxx : hE σ J x x = 0) :
    ∃ y, hE σ J x y = 1 ∧ hE σ J y y = 0 := by
  have hr : Matrix.vecMul (fun i => σ (x i)) J ≠ 0 := by
    intro h0
    have h1 := Matrix.eq_zero_of_vecMul_eq_zero hJ.2 h0
    apply hx
    funext i
    have h3 := congrFun h1 i
    simpa using h3
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hr
  have hj' : Matrix.vecMul (fun i => σ (x i)) J j ≠ 0 := hj
  obtain ⟨y₀, h1⟩ : ∃ y₀, hE σ J x y₀ = 1 := by
    refine ⟨Pi.single j (Matrix.vecMul (fun i => σ (x i)) J j)⁻¹, ?_⟩
    rw [hE_eq_dot, dotProduct_single, mul_inv_cancel₀ hj']
  have conj := hE_conj (J := J) hσ hJ.1
  have h1' : hE σ J y₀ x = 1 := by rw [← conj, h1, map_one]
  have hc : σ (hE σ J y₀ y₀) = hE σ J y₀ y₀ := conj _ _
  set c := hE σ J y₀ y₀ with hcdef
  have hc2 : σ (c / 2) = c / 2 := by rw [map_div₀, hc, map_ofNat]
  have hxy : hE σ J x (y₀ - (c / 2) • x) = 1 := by
    have := (hLin σ J x).map_sub y₀ ((c / 2) • x)
    simp only [map_smul, hLin_apply, smul_eq_mul, hxx, h1] at this
    simpa using this
  have hy₀y : hE σ J y₀ (y₀ - (c / 2) • x) = c / 2 := by
    have := (hLin σ J y₀).map_sub y₀ ((c / 2) • x)
    simp only [map_smul, hLin_apply, smul_eq_mul, h1', ← hcdef] at this
    rw [this]; field_simp; ring
  refine ⟨y₀ - (c / 2) • x, hxy, ?_⟩
  have := (hLin σ J (y₀ - (c / 2) • x)).map_sub y₀ ((c / 2) • x)
  simp only [map_smul, hLin_apply, smul_eq_mul] at this
  rw [this, ← conj y₀, hy₀y, hc2, ← conj x, hxy, map_one]
  ring

theorem finrank_perp (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j)
    {x y : Fin M → E} (hxx : hE σ J x x = 0) (hyy : hE σ J y y = 0) (hxy : hE σ J x y = 1) :
    Module.finrank E (LinearMap.ker ((hLin σ J x).prod (hLin σ J y))) + 2 = M := by
  have hyx : hE σ J y x = 1 := by rw [← hE_conj hσ hJ, hxy, map_one]
  have hs : Function.Surjective ((hLin σ J x).prod (hLin σ J y)) := by
    rintro ⟨a, b⟩
    refine ⟨a • y + b • x, Prod.ext ?_ ?_⟩
    · change hLin σ J x (a • y + b • x) = a
      simp only [map_add (f := _), map_smul, hLin_apply, smul_eq_mul, hxy, hxx, mul_one, mul_zero, add_zero]
    · change hLin σ J y (a • y + b • x) = b
      simp only [map_add (f := _), map_smul, hLin_apply, smul_eq_mul, hyy, hyx, mul_one, mul_zero, zero_add]
  have h := LinearMap.finrank_range_add_finrank_ker ((hLin σ J x).prod (hLin σ J y))
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_prod, Module.finrank_self,
    Module.finrank_fin_fun] at h
  omega

theorem gram_eq {n : ℕ} (c : Fin n → Fin M → E) :
    cT (σ : E →+* E) (Matrix.of c)ᵀ * J * (Matrix.of c)ᵀ = gramE σ J c := by
  ext a b
  simp only [Matrix.mul_apply, cT, gramE, hE, hform, Finset.sum_mul, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.of_apply]
  exact Finset.sum_comm

theorem det_ne_zero_of_hypJ {M₁ : ℕ} (A : Matrix (Fin M₁) (Fin M₁) E) (h : (hypJ A).det ≠ 0) :
    A.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply h
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨Fin.cons 0 (Fin.cons 0 v), ?_, ?_⟩
  · intro h1
    apply hv
    funext i
    simpa using congrFun h1 i.succ.succ
  · funext a
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun a => ?_) a) a
    · simp [Matrix.mulVec, dotProduct, hypJ, Fin.sum_univ_succ]
    · simp [Matrix.mulVec, dotProduct, hypJ, Fin.sum_univ_succ]
    · have := congrFun hAv a
      simpa [Matrix.mulVec, dotProduct, hypJ, Fin.sum_univ_succ] using this

theorem selfDualLattice_projection_mem_of_unit_length (hσ : ∀ a, σ (σ a) = a) (h2 : (2 : E) ≠ 0) {M₁ : ℕ}
    {J : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E} (hJ : IsHermND σ J)
    {x y : Fin (M₁ + 2) → E} (hxx : hE σ J x x = 0) (hyy : hE σ J y y = 0)
    (hxy : hE σ J x y = 1) :
    ∃ (g : GL (Fin (M₁ + 2)) E) (J₁ : Matrix (Fin M₁) (Fin M₁) E), IsHermND σ J₁ ∧
      hypJ J₁ = cT (σ : E →+* E) (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) * J *
        (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) := by
  have conj := hE_conj (J := J) hσ hJ.1
  have hyx : hE σ J y x = 1 := by rw [← conj, hxy, map_one]
  have hfr := finrank_perp hσ hJ.1 hxx hyy hxy
  set W := LinearMap.ker ((hLin σ J x).prod (hLin σ J y)) with hW
  have hfr' : Module.finrank E W = M₁ := by omega
  let b : Module.Basis (Fin M₁) E W := Module.finBasisOfFinrankEq E W hfr'
  have hbx : ∀ i, hE σ J x (b i : Fin (M₁ + 2) → E) = 0 := fun i => by
    have h3 : ((hLin σ J x).prod (hLin σ J y)) (b i : Fin (M₁ + 2) → E) = 0 :=
      LinearMap.mem_ker.mp (b i).2
    exact congrArg Prod.fst h3
  have hby : ∀ i, hE σ J y (b i : Fin (M₁ + 2) → E) = 0 := fun i => by
    have h3 : ((hLin σ J x).prod (hLin σ J y)) (b i : Fin (M₁ + 2) → E) = 0 :=
      LinearMap.mem_ker.mp (b i).2
    exact congrArg Prod.snd h3
  have hbx' : ∀ i, hE σ J (b i : Fin (M₁ + 2) → E) x = 0 := fun i => by
    rw [← conj, hbx, map_zero]
  have hby' : ∀ i, hE σ J (b i : Fin (M₁ + 2) → E) y = 0 := fun i => by
    rw [← conj, hby, map_zero]
  let c : Fin (M₁ + 2) → Fin (M₁ + 2) → E :=
    Fin.cons x (Fin.cons y fun i => (b i : Fin (M₁ + 2) → E))
  have hli : LinearIndependent E c := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at ha
    simp only [c, Fin.cons_zero, Fin.cons_succ] at ha
    have e1 := congrArg (hLin σ J x) ha
    have e2 := congrArg (hLin σ J y) ha

    simp only [map_add (f := _), map_smul, map_sum, hLin_apply, smul_eq_mul, hxx, hyy, hxy, hyx, hbx, hby,
    map_zero, mul_zero, zero_add, add_zero, mul_one, Finset.sum_const_zero] at e1 e2
    rw [e1, e2] at ha
    simp only [zero_smul, zero_add] at ha
    have e3 : ∑ i, a i.succ.succ • b i = 0 := by
      apply Subtype.ext
      simpa using ha
    have e4 := Fintype.linearIndependent_iff.mp b.linearIndependent _ e3
    intro i
    refine Fin.cases e2 (fun i => Fin.cases e1 e4 i) i
  have hunit : IsUnit (Matrix.of c)ᵀ := by
    exact (Matrix.linearIndependent_cols_iff_isUnit (A := (Matrix.of c)ᵀ)).mp hli
  let J₁ : Matrix (Fin M₁) (Fin M₁) E := gramE σ J fun i => (b i : Fin (M₁ + 2) → E)
  have hgram : hypJ J₁ = gramE σ J c := by
    ext a b'
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun a => ?_) a) a <;>
      refine Fin.cases ?_ (fun b' => Fin.cases ?_ (fun b' => ?_) b') b' <;>
      simp [hypJ, gramE, c, J₁, hxx, hyy, hxy, hyx, hbx, hby, hbx', hby']
  have hdet : (hypJ J₁).det ≠ 0 := by
    rw [hgram, ← gram_eq, Matrix.det_mul, Matrix.det_mul]
    have hu : (Matrix.of c)ᵀ.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero
    have hcT : (cT (σ : E →+* E) (Matrix.of c)ᵀ).det ≠ 0 := by
      rw [cT, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      simpa using hu
    exact mul_ne_zero (mul_ne_zero hcT hJ.2) hu
  refine ⟨hunit.unit, J₁, ⟨fun i j => conj _ _, det_ne_zero_of_hypJ J₁ hdet⟩, ?_⟩
  rw [hgram, ← gram_eq]
  rfl

end Alg

theorem sigma_invol {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (a : E) : σ (σ a) = a := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem splitHyp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin M → E, x ≠ 0 → hE σ J x x = 0 → ∃ (M₁ : ℕ) (hM : M = M₁ + 2) (g : GL (Fin (M₁ + 2)) E) (J₁ : Matrix (Fin M₁) (Fin M₁) E), IsHermND σ J₁ ∧ hypJ J₁ = cT (σ : E →+* E) (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) * (hM ▸ J) * (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) := by
  intro F E _ _ _ _ _ σ hcm M J hJ x hx hxx
  have hσ := sigma_invol σ hcm
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  obtain ⟨y, hxy, hyy⟩ := exists_partner hσ hJ h2 x hx hxx
  have hfr := finrank_perp hσ hJ.1 hxx hyy hxy
  obtain ⟨M₁, rfl⟩ : ∃ M₁, M = M₁ + 2 := ⟨_, hfr.symm⟩
  obtain ⟨g, J₁, h1, h3⟩ := selfDualLattice_projection_mem_of_unit_length hσ h2 hJ hxx hyy hxy
  exact ⟨M₁, rfl, g, J₁, h1, h3⟩

end GlobalTheory.CompanionTheory.SW.HypSplit
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IsotropicVectorSplitsHyperbolicPlaneStatement

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.isotropic_vector_splits_hyperbolic_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin M → E, x ≠ 0 → hE σ J x x = 0 → ∃ (M₁ : ℕ) (hM : M = M₁ + 2) (g : GL (Fin (M₁ + 2)) E) (J₁ : Matrix (Fin M₁) (Fin M₁) E), IsHermND σ J₁ ∧ hypJ J₁ = cT (σ : E →+* E) (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) * (hM ▸ J) * (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) := by
  first | exact @GlobalTheory.CompanionTheory.SW.HypSplit.splitHyp | exact GlobalTheory.CompanionTheory.SW.HypSplit.splitHyp | (intros; apply GlobalTheory.CompanionTheory.SW.HypSplit.splitHyp <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CountingRationalVectorsBoxBound

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.IsoBox

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem hform_eq_dot {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (s : A →+* A)
    (J : Matrix n n A) (x y : n → A) :
    hform s J x y = (fun i => s (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (s : A →+* A)
    (J g : Matrix n n A) (x y : n → A) :
    hform s J (g *ᵥ x) (g *ᵥ y) = hform s (cT s g * J * g) x y := by
  rw [hform_eq_dot, hform_eq_dot, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec (fun i => s (x i)) (cT s g)]
  congr 1
  ext i
  simp [cT, Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]

theorem gramE_mulVec (σ : E →ₐ[F] E) {M n : ℕ} (J g : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → E) :
    gramE σ J (fun a => g *ᵥ X a) = gramE σ (cT (σ : E →+* E) g * J * g) X := by
  funext a c
  exact hform_mulVec (σ : E →+* E) J g (X a) (X c)

theorem isotropic_preimage (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (g : GL (Fin M) E) :
    {X : Fin 1 → Fin M → E | (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X a) ∈
        {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0}} =
      {X : Fin 1 → Fin M → E | X ≠ 0 ∧
        gramE σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J *
          (g : Matrix (Fin M) (Fin M) E)) X = 0} := by
  ext X
  simp only [Set.mem_ofPred_eq, gramE_mulVec]
  refine and_congr_left fun _ => not_congr ?_
  constructor
  · intro h
    funext a
    have h1 := congrFun h a
    have h2 : ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ
        ((g : Matrix (Fin M) (Fin M) E) *ᵥ X a) = X a := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel]
      simp
    rw [← h2]
    simp only [Pi.zero_apply] at h1 ⊢
    rw [h1, Matrix.mulVec_zero]
  · intro h
    funext a
    simp [h]

theorem actTup_smul (R : Type) [CommRing R] [Algebra F R] {M n : ℕ} (g : GL (Fin M) (R ⊗[F] E))
    (c : R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E) :
    actTup R g (c • Y) = c • actTup R g Y := by
  funext a
  simp [actTup, Matrix.mulVec_smul]

theorem continuous_actTup (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing (R ⊗[F] E)] {M n : ℕ} (g : GL (Fin M) (R ⊗[F] E)) :
    Continuous (actTup R g : (Fin n → Fin M → R ⊗[F] E) → _) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simp only [actTup, Matrix.mulVec, dotProduct]
  refine continuous_finsetSum _ fun j _ => ?_
  exact continuous_const.mul ((continuous_apply j).comp (continuous_apply a))

end GlobalTheory.CompanionTheory.SW.IsoBox

namespace GlobalTheory.CompanionTheory.SW

theorem mean_isotropic_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (N : ℕ), 0 < N → ∃ C : ℝ, ∀ r : ℝ, 0 < r → cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0} (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) ≤ ENNReal.ofReal (C * r ^ (2 * Module.finrank ℚ F * (M - 1))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM μ 𝓕 hH hF d b N hN
  by_cases hiso : ∃ x : Fin M → E, x ≠ 0 ∧ hE σ J x x = 0
  · obtain ⟨x, hx, hxx⟩ := hiso
    obtain ⟨M₁, hM₁, g, J₁, hJ₁, hg⟩ := GlobalTheory.T.isotropic_vector_splits_hyperbolic_plane F E σ hCM M J hJ x hx hxx
    subst hM₁
    obtain ⟨μ', 𝓕', hH', hF', -, hT⟩ :=
      GlobalTheory.T.fundamental_domain_transport_congruent_form F E σ hCM (M₁ + 2) J hJ g (hypJ J₁) hg μ 𝓕 hH hF
    obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_real_flow_adelic_units F E σ hCM
    obtain ⟨hbc, -, hsc⟩ := GlobalTheory.T.adelic_boxes_compact_exhaust F E σ hCM d b 1 (M₁ + 2)
    obtain ⟨⟨hA1, hA2, hA3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
    have := hA1
    have := hA2
    have := hA3
    have : IsTopologicalRing (AF F ⊗[F] E) :=
      (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)).1
    set G : GL (Fin (M₁ + 2)) (AF F ⊗[F] E) := bc (inclR (AF F)) g with hG
    have hΩ : IsCompact (actTup (AF F) G ⁻¹' (box b N 1 : Set (Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E))) := by
      have himg : actTup (AF F) G ⁻¹' (box b N 1 : Set (Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E)) =
          actTup (AF F) G⁻¹ '' box b N 1 := by
        ext Y
        constructor
        · intro hY
          refine ⟨_, hY, ?_⟩
          funext a
          simp [actTup, Matrix.mulVec_mulVec]
        · rintro ⟨Z, hZ, rfl⟩
          have : actTup (AF F) G (actTup (AF F) G⁻¹ Z) = Z := by
            funext a
            simp [actTup, Matrix.mulVec_mulVec]
          simpa [Set.mem_preimage, this] using hZ
      rw [himg]
      exact (hbc N 1 hN).image (IsoBox.continuous_actTup (AF F) G⁻¹)
    obtain ⟨C, hC⟩ := GlobalTheory.T.hyperbolic_finite_volume_integral_bound F E σ hCM M₁ J₁ hJ₁ (by omega)
      (GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hCM M₁ J₁ hJ₁) τ hτ μ' 𝓕' hH' hF' _ hΩ
    refine ⟨C, fun r hr => ?_⟩
    have hfun : (fun Y : Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E =>
          Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞)) (actTup (AF F) G Y)) =
        fun Y => (Set.indicator (actTup (AF F) G ⁻¹' box b N 1) (fun _ => (1 : ℝ≥0∞)))
          (((τ (Multiplicative.ofAdd (-Real.log r)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • Y) := by
      funext Y
      have hmem : actTup (AF F) G Y ∈ (box b N r : Set (Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E)) ↔
          ((τ (Multiplicative.ofAdd (-Real.log r)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • Y ∈
            actTup (AF F) G ⁻¹' (box b N 1 : Set (Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E)) := by
        have h := hsc τ hτ N r (-Real.log r) (actTup (AF F) G Y)
        have h1 : Real.exp (-Real.log r) * r = 1 := by
          rw [Real.exp_neg, Real.exp_log hr]
          exact inv_mul_cancel₀ hr.ne'
        rw [h1] at h
        rw [Set.mem_preimage, IsoBox.actTup_smul]
        exact h.symm
      by_cases hY : actTup (AF F) G Y ∈ (box b N r : Set (Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E))
      · rw [Set.indicator_of_mem hY, Set.indicator_of_mem (hmem.1 hY)]
      · rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem (fun h => hY (hmem.2 h))]
    have hset := IsoBox.isotropic_preimage σ J g
    rw [← hg] at hset
    rw [hT 1, hset, hfun]
    simpa using hC r hr
  · refine ⟨0, fun r _ => ?_⟩
    have hempty : {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0} = ∅ := by
      ext X
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hX hgr
      apply hiso
      refine ⟨X 0, fun h0 => hX ?_, congrFun (congrFun hgr 0) 0⟩
      funext a
      rw [Subsingleton.elim a 0, h0]
      rfl
    simp [cntI, hempty]

end GlobalTheory.CompanionTheory.SW
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CountingRationalVectorsBoxBoundStatement

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.isotropic_vector_count_box_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (N : ℕ), 0 < N → ∃ C : ℝ, ∀ r : ℝ, 0 < r → cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0} (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) ≤ ENNReal.ofReal (C * r ^ (2 * Module.finrank ℚ F * (M - 1))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.mean_isotropic_box | exact GlobalTheory.CompanionTheory.SW.mean_isotropic_box | (intros; apply GlobalTheory.CompanionTheory.SW.mean_isotropic_box <;> assumption)
end
end
