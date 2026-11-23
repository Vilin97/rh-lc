module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundOfNatDegree
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountLeOfDvd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetLIntegralLeOfBound
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
public import GroundTheory.AutomorphicForms.ReductionSplitting
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsLintegralConstantTermL2SqLe
import GroundTheory.AutomorphicForms.ReductionFinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UpdateLeUpdate
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.AutomorphicLipschitz.NiceAut
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ConjugationDifferences.ExpDivExpEq
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ConstantTermSteps.CtstepglueHolds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExponentialGluing.ExpNegGlueHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRightHaarMeasure
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2Gluing.IntegralLeToReal
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SquareIntegrableCovers.SetLIntegralLeOfCover

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SingleVecMulUnipMatrix

section

@[expose] public section

noncomputable section

open NumberField Filter Topology Matrix
open scoped NumberField.AdeleRing
open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
  GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Rs.An

namespace GlobalTheory.CompanionTheory.SiegelEscape

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem exists_eq_of_mem_lat {γ : AdelicGLn.AdelicGL K n} (hγ : γ ∈ lat K n) :
    ∃ (γ₀ : GL (Fin n) K) (u : IdeleGroup K),
      γ = AdelicGLn.diagonal K n γ₀ * scalarUnits K n u := by
  set s : IdeleGroup K := posIdele (Real.exp 1) (Real.exp_pos _) with hs
  have hz : (tor K fun _ : Fin n => (1 : ℝ)) = scalarUnits K n s := rfl
  have hN : (Subgroup.zpowers (tor K fun _ : Fin n => (1 : ℝ))).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [hz, ← map_zpow, ← scalarUnits_mul_comm, mul_inv_cancel_right, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ _
  have h := Subgroup.mul_normal (AdelicGLn.diagonal K n).range
    (Subgroup.zpowers (tor K fun _ : Fin n => (1 : ℝ)))
  have hγ' : γ ∈ (↑((AdelicGLn.diagonal K n).range ⊔
      Subgroup.zpowers (tor K fun _ : Fin n => (1 : ℝ))) : Set (AdelicGLn.AdelicGL K n)) := hγ
  rw [h] at hγ'
  obtain ⟨a, ⟨γ₀, rfl⟩, b, hb, rfl⟩ := Set.mem_mul.1 hγ'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  exact ⟨γ₀, s ^ k, by rw [hz, map_zpow]⟩

theorem detModule_scalarUnits (u : IdeleGroup K) :
    (detModule K n (scalarUnits K n u) : ℝ) = (ideleModule K u : ℝ) ^ n := by
  rw [detModule, MonoidHom.comp_apply, scalarUnits_apply, det_diagUnits, map_prod,
    coe_finset_prod_pos]
  simp

theorem detModule_unipGL {r : ℕ} (X : UPos n r → 𝔸[K]) : detModule K n (unipGL X) = 1 :=
  mem_normOneGL_iff_detModule.1 (unipGL_mem_normOneGL X)

theorem detModule_diagonal (γ₀ : GL (Fin n) K) : detModule K n (AdelicGLn.diagonal K n γ₀) = 1 :=
  mem_normOneGL_iff_detModule.1 (rationalGL_le_normOneGL ⟨γ₀, rfl⟩)

theorem detModule_aR {r : ℕ} (hr : r ≤ n) (t : ℝ) :
    (detModule K n (aR K n r t) : ℝ) = Real.exp (r * t) ^ Module.finrank ℚ K := by
  have h := ideleModule_det_diagUnits_posIdele (K := K) (n := n)
    (fun i : Fin n => Real.exp (if (i : ℕ) < r then t else 0)) (fun _ => Real.exp_pos _)
  have h2 : ∏ i : Fin n, Real.exp (if (i : ℕ) < r then t else 0) = Real.exp (r * t) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 2
    simp [Fin.card_filter_val_lt, hr]
  rw [h2] at h
  exact h

theorem ratVec_single (l : Fin n) : ratVec (Pi.single l (1 : K)) = Pi.single l (1 : 𝔸[K]) := by
  ext1 i
  by_cases h : i = l
  · subst h; simp [ratVec]
  · simp [ratVec, h]

theorem single_vecMul_unipMatrix {r : ℕ} {l : Fin n} (hl : r ≤ (l : ℕ)) (X : UPos n r → 𝔸[K]) :
    Pi.single l (1 : 𝔸[K]) ᵥ* unipMatrix X = Pi.single l (1 : 𝔸[K]) := by
  have h : ¬ ((l : ℕ) < r) := by omega
  ext1 j
  rw [Matrix.single_one_vecMul]
  simp [unipMatrix, blockEntry_apply, h, Matrix.one_apply, Pi.single_apply, eq_comm]

theorem single_vecMul_aR {r : ℕ} {l : Fin n} (hl : r ≤ (l : ℕ)) (t : ℝ) :
    Pi.single l (1 : 𝔸[K]) ᵥ* ((aR K n r t : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) =
      Pi.single l (1 : 𝔸[K]) := by
  have h : ¬ ((l : ℕ) < r) := by omega
  have h1 : ∀ (ρ : ℝ) (hρ : 0 < ρ), ρ = 1 → posIdele (K := K) ρ hρ = 1 := by
    rintro _ _ rfl
    exact map_one (posIdeleHom K)
  rw [aR, tor, coe_diagUnits]
  ext1 j
  rw [Matrix.vecMul_diagonal]
  by_cases hj : j = l
  · subst hj
    rw [h1 _ _ (by simp [h])]
    simp
  · simp [Pi.single_apply, hj]

theorem height_eq {r : ℕ} {l : Fin n} (hl : r ≤ (l : ℕ)) (γ₀ : GL (Fin n) K) (u : IdeleGroup K)
    (X : UPos n r → 𝔸[K]) (t : ℝ) (q : AdelicGLn.AdelicGL K n) :
    Reduction.height (AdelicGLn.diagonal K n γ₀ * scalarUnits K n u * (unipGL X * aR K n r t * q))
        (Pi.single l (1 : K) ᵥ* ((γ₀⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      (ideleModule K u : ℝ) *
        adelicNorm (Pi.single l (1 : 𝔸[K]) ᵥ* (q : Matrix (Fin n) (Fin n) 𝔸[K])) := by
  rw [mul_assoc, height_diagonal_mul, Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.vecMul_one, Reduction.height, ratVec_single, Units.val_mul, Units.val_mul,
    Units.val_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
    coe_unipGL, scalarUnits_apply, coe_diagUnits]
  have h0 : Pi.single l (1 : 𝔸[K]) ᵥ* Matrix.diagonal (fun _ : Fin n => ((u : IdeleGroup K) : 𝔸[K])) =
      ((u : IdeleGroup K) : 𝔸[K]) • Pi.single l (1 : 𝔸[K]) := by
    ext1 j
    rw [Matrix.vecMul_diagonal]
    simp [mul_comm]
  rw [h0, Matrix.smul_vecMul, Matrix.smul_vecMul, Matrix.smul_vecMul, single_vecMul_unipMatrix hl,
    single_vecMul_aR hl]
  have hne : (Pi.single l (1 : K) : Fin n → K) ≠ 0 := by
    intro h
    have := congrFun h l
    simp at this
  have hfc := hasFiniteContent_height q hne
  rw [ratVec_single] at hfc
  exact adelicNorm_smul hfc u

theorem escape : Escape := by
  intro K _ _ n r hr hrn D Q T hD hQ hT
  have hn : 0 < n := by omega
  set l : Fin n := ⟨n - 1, by omega⟩ with hldef
  have hl : r ≤ (l : ℕ) := by simp only [hldef]; omega
  set e : Fin n → K := Pi.single l 1 with he
  have he0 : e ≠ 0 := by
    intro h
    have := congrFun h l
    simp [he] at this
  obtain ⟨ε, hε, hheight⟩ := exists_pos_le_height hT
  obtain ⟨P, hP, hvec⟩ := exists_adelicNorm_vecMul_le_mul hQ
  set A : ℝ := adelicNorm (ratVec e) with hA
  have hA1 : 1 ≤ A := one_le_adelicNorm_ratVec he0
  have hcont : Continuous fun g : AdelicGLn.AdelicGL K n => (detModule K n g : ℝ) :=
    continuous_subtype_val.comp continuous_detModule
  obtain ⟨_, B, -, -, hB⟩ := exists_pos_bounds hT hcont fun g _ => (detModule K n g).2
  obtain ⟨b, _, hb, -, hb'⟩ := exists_pos_bounds hQ hcont fun g _ => (detModule K n g).2
  set c : ℝ := ε / (P * A) with hc
  have hPA : 0 < P * A := mul_pos hP (by linarith)
  have hcpos : 0 < c := div_pos hε hPA
  set d := Module.finrank ℚ K with hd
  have hd0 : d ≠ 0 := Module.finrank_pos.ne'
  have hr0 : (0 : ℝ) < r := Nat.cast_pos.2 hr
  have htend : Tendsto (fun t : ℝ => Real.exp (r * t) ^ d) atTop atTop :=
    (tendsto_pow_atTop hd0).comp
      (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hr0))
  filter_upwards [htend.eventually_gt_atTop (B / (c ^ n * b))] with t ht γ hγ X _ q hq hmem
  obtain ⟨γ₀, u, rfl⟩ := exists_eq_of_mem_lat hγ
  set E : ℝ := (ideleModule K u : ℝ) with hE
  have hEpos : 0 < E := (ideleModule K u).2
  set τ := AdelicGLn.diagonal K n γ₀ * scalarUnits K n u * (unipGL X * aR K n r t * q) with hτ
  have hx0 : (e ᵥ* ((γ₀⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ≠ 0 := by
    intro h
    apply he0
    have h2 := congrArg (· ᵥ* ((γ₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) h
    simpa [Matrix.vecMul_vecMul, ← Units.val_mul] using h2
  have h1 : ε ≤ E * (P * A) := by
    have h2 := hheight τ hmem _ hx0
    rw [hτ, height_eq hl] at h2
    have h3 := hvec q hq (ratVec e) (hasFiniteContent_ratVec he0)
    rw [he, ratVec_single] at h3
    rw [hA, he, ratVec_single]
    exact h2.trans (mul_le_mul_of_nonneg_left h3 hEpos.le)
  have hcE : c ≤ E := (div_le_iff₀ hPA).2 h1
  have hdet : (detModule K n τ : ℝ) = E ^ n * (Real.exp (r * t) ^ d * (detModule K n q : ℝ)) := by
    rw [hτ, map_mul, map_mul, map_mul, map_mul, detModule_diagonal, detModule_unipGL, one_mul,
      one_mul, Positive.val_mul, Positive.val_mul, detModule_scalarUnits, detModule_aR hrn.le]
  have hle := (hB τ hmem).2
  rw [hdet] at hle
  have hbq := (hb' q hq).1
  have hexp : 0 < Real.exp (r * t) ^ d := pow_pos (Real.exp_pos _) _
  have hcn : 0 < c ^ n := pow_pos hcpos _
  have h4 : c ^ n * (Real.exp (r * t) ^ d * b) ≤ B := by
    refine le_trans ?_ hle
    exact mul_le_mul (pow_le_pow_left₀ hcpos.le hcE n)
      (mul_le_mul_of_nonneg_left hbq hexp.le) (mul_pos hexp hb).le (pow_pos hEpos _).le
  rw [div_lt_iff₀ (mul_pos hcn hb)] at ht
  nlinarith [ht, h4]

end GlobalTheory.CompanionTheory.SiegelEscape

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.GapPairings.GapGlue

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep.CuspidalL2GL

namespace PositivityTheory.Rg.Rs.JGapGlue

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def locRep (V : Submodule ℂ (Sm E a)) (hs : _root_.GlobalTheory.CuspRep.IsStable V) (w : HeightOneSpectrum (𝓞 E)) :
    Representation ℂ (GL (Fin a) (w.adicCompletion E)) V where
  toFun g := (finRep E a (locGL E a w g)).restrict fun ψ hψ => hs (.fin (locGL E a w g)) ψ hψ
  map_one' := by
    ext ψ
    simp
  map_mul' g h := by
    ext ψ
    simp only [map_mul]
    rfl

def pairing {X W : Type} [AddCommGroup X] [Module ℂ X] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (F : X →ₗ[ℂ] W) : X →ₗ[ℂ] X →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => inner ℂ (F y) (F x))
    (fun x x' y => by simp only [map_add (f := _), inner_add_right])
    (fun c x y => by simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply])
    (fun x y y' => by simp only [map_add (f := _), inner_add_left])
    (fun c x y => by simp only [map_smul, inner_smul_left, smul_eq_mul])

theorem pairing_apply {X W : Type} [AddCommGroup X] [Module ℂ X] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (F : X →ₗ[ℂ] W) (x y : X) : pairing F x y = inner ℂ (F y) (F x) := rfl

theorem gap (hL : LatOf) (hG : GapAbs) : Gap := by
  intro E _ _ _ N V hV w B hB z hz
  obtain ⟨⟨φ, hφV, hsat⟩, -⟩ := hB
  have hcard : B.card = N := hsat.2.2.1
  cases N with
  | zero =>
    rw [Multiset.card_eq_zero] at hcard
    subst hcard
    simp
  | succ n =>
    obtain ⟨μ, h1, h2⟩ := GlobalTheory.CompanionTheory.AdelicHaar.exists_haar_rightInvariant E (n + 1)
    have hm : ∀ ψ ∈ V, MemL2Quotient (latticeGL E (n + 1)) μ ψ.1 := fun ψ hψ =>
      memL2_of_isAutForm (hV.aut ψ hψ) (hV.sqInt ψ hψ)
    have hi : Function.Injective (toL2ₗ μ V hm) :=
      toL2ₗ_injective hm fun ψ hψ => ContAut.continuous_of_isOpen_stab E _ ψ (hV.aut ψ hψ).level
    set F := toL2ₗ μ V hm with hF
    let ρ := locRep V hV.stable w
    have hρ : ∀ g (y : V), F (ρ g y) = R (latticeGL E (n + 1)) μ (finGL E (n + 1) (locGL E (n + 1) w g)) (F y) :=
      fun g y => (R_toL2ₗ hm y (hV.stable (.fin (locGL E (n + 1) w g)) y.1 y.2)).symm
    have hsatV : GlobalTheory.LFun.IsSatVecGL w ρ ⟨φ, hφV⟩ B :=
      GlobalTheory.LFun.IsSatVecGL.of_map V.subtype (fun g y => rfl) Subtype.val_injective hsat
    have herm : ∀ x y, pairing F y x = starRingEnd ℂ (pairing F x y) := fun x y => by
      rw [pairing_apply, pairing_apply, inner_conj_symm]
    have pos : ∀ x, x ≠ 0 → 0 < (pairing F x x).re := fun x hx => by
      rw [pairing_apply]
      have h0 : F x ≠ 0 := fun h => hx (hi (h.trans (map_zero F).symm))
      have hn : 0 < ‖F x‖ := norm_pos_iff.2 h0
      have e := inner_self_eq_norm_sq (𝕜 := ℂ) (F x)
      change 0 < RCLike.re (inner ℂ (F x) (F x))
      rw [e]
      positivity
    have unit : ∀ g x y, pairing F (ρ g x) (ρ g y) = pairing F x y := fun g x y => by
      rw [pairing_apply, pairing_apply, hρ, hρ]
      let I : L2 (latticeGL E (n + 1)) μ →ₗᵢ[ℂ] L2 (latticeGL E (n + 1)) μ :=
        { toLinearMap := (R (latticeGL E (n + 1)) μ (finGL E (n + 1) (locGL E (n + 1) w g))).toLinearMap
          norm_map' := norm_R _ }
      exact I.inner_map_map (F y) (F x)
    obtain ⟨k, _, _, Γ, _, red, ρ', t, v, hk, hD, hE⟩ := hL E w n V ρ (pairing F) ⟨φ, hφV⟩ B herm pos unit hsatV
    have h0 : (0 : ℂ) ∉ B.map fun b : ℂˣ => (b : ℂ) := by
      simp
    have := hG k n V Γ (pairing F) red ρ' t v _ hD hE h0 z (by rw [hk]; exact_mod_cast hz)
    rw [hk] at this
    exact_mod_cast this

end PositivityTheory.Rg.Rs.JGapGlue

namespace PositivityTheory.Rg.Rs

theorem gapGlue_holds : GapGlue := JGapGlue.gap

end PositivityTheory.Rg.Rs
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SqIntCritOf

section

@[expose] public section

namespace PositivityTheory.Rg.Rs

theorem expNeg_of (h : An.Count) : ExpNeg :=
  expNegGlue_holds dict_holds (l2glue_holds h GlobalTheory.CompanionTheory.SiegelEscape.escape)

theorem sqIntCrit_of (h1 : InitBnd) (h2 : FinTr) (h3 : An.BoxVol) : SqIntCrit :=
  sqIntGlue_holds dict_holds niceAut_holds h1 h2 killPoly_holds
    (GlobalTheory.CompanionTheory.AnBoot.bootGlue diffstep_holds (ctstepglue_holds GlobalTheory.CompanionTheory.LinRec.recBound)) (GlobalTheory.CompanionTheory.SlabGlue.slabGlue h3)

theorem gap_of (h1 : LatOf) (h2 : GapOp) : Gap :=
  gapGlue_holds h1 (gapAbs_of h2 GlobalTheory.CompanionTheory.GapPolyProof.gapPoly)

end PositivityTheory.Rg.Rs
end
end
