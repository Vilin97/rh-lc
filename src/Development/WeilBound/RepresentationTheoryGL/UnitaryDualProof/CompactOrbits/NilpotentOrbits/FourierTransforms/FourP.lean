module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseP
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.ContinuousQZ
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.CompP
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.FourierTransformPreservesCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.IsSemisimpleRing
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.TraceEqZeroOfQZ
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.RingTheory.WittVector.IsPoly
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.TraceEqZeroOfQZ

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.FourierTransformInvolution

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.RgUd.T.Nil.Four.Phi2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}
  [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
  (hZ : CR Z) (h : Hyp Z)

include hZ h

theorem fourier_transform_involution {c : kˣ} (hc : HasConductor ψ c) {f : Sp k n → ℂ}
    (hf : f ∈ supportedIn (Set.univ : Set (Sp k n))) (p : Sp k n) :
    phi0 ψ ν hZ h (phi0 ψ ν hZ h f) p =
      ((distribHaarChar k (Matrix.GeneralLinearGroup.det (Gu hZ h)) : ℝ) : ℂ)⁻¹ *
        ((((ν.real (𝒪[k] : Set k) ^ 2 * nabs k c) ^ (d Z) : ℝ)) : ℂ) * f (Refl (Z := Z) p) := by
  have h1 : (fun q => f (F1 hZ h q)) ∈ SB (TT Z × (Fin (d Z) → k)) :=
    (GlobalTheory.SplitDict.bijOn_comp (F1 hZ h)).1 hf.1
  have e : ∀ q, phi0 ψ ν hZ h f (F1 hZ h q) =
      GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ => ν) (fun q => f (F1 hZ h q)) (q.1, G Z *ᵥ q.2) := by
    intro q
    show GlobalTheory.SplitDict.pf _ _ _ (Hb hZ h (F1 hZ h q)) = _
    rw [partial_fourier_first_coordinates]
  show GlobalTheory.SplitDict.pf ψ _ (fun q => phi0 ψ ν hZ h f (F1 hZ h q)) (Hb hZ h p) = _
  simp only [e]
  show ∫ u, GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ => ν) (fun q => f (F1 hZ h q)) ((Hb hZ h p).1, G Z *ᵥ u) *
      (ψ (u ⬝ᵥ (Hb hZ h p).2) : ℂ) ∂(Measure.pi fun _ => ν) = _
  rw [pf_G ψ ν hZ h, GlobalTheory.SplitDict.pf_pf ν hc h1]
  simp only [real_test_function_apply, Fintype.card_fin]
  have e2 : ((Hb hZ h p).1.1 : Matrix (Fin n) (Fin n) k) + E Z (-((G Z)⁻¹ *ᵥ (Hb hZ h p).2)) =
      p.1 - (2 : k) • Pr Z p.1 := by
    rw [E_neg]
    show p.1 - Pr Z p.1 + -(E Z ((G Z)⁻¹ *ᵥ D Z p.1)) = _
    rw [← Pr, two_smul]
    abel
  have e3 : (Hb hZ h p).1.2 = p.2 := rfl
  rw [e2, e3]
  simp only [Refl]
  ring

def Tu (t : kˣ) : GL (Fin (d Z)) k := Units.map (Matrix.scalar (Fin (d Z)) : k →+* Matrix (Fin (d Z)) (Fin (d Z)) k) t

omit hZ h [MeasurableSpace k] [BorelSpace k] [ν.IsAddHaarMeasure] in
theorem Tu_mulVec (t : kˣ) (u : Fin (d Z) → k) : (Tu (Z := Z) t).val *ᵥ u = (t : k) • u := by
  funext i
  simp [Tu, Matrix.scalar_apply, mulVec_diagonal]

omit hZ h [MeasurableSpace k] [BorelSpace k] [ν.IsAddHaarMeasure] in
theorem Tu_det (t : kˣ) : Matrix.GeneralLinearGroup.det (Tu (Z := Z) t) = t ^ d Z := by
  ext
  simp [Tu, Matrix.scalar_apply, Matrix.GeneralLinearGroup.val_det_apply, det_diagonal]

theorem fourier_transform_scaling (t : kˣ) (f : Sp k n → ℂ) {p : Sp k n} (hp : p ∈ Bz Z ×ˢ Set.univ) :
    phi0 ψ ν hZ h f (sig Z t p) =
      ((((nabs k t)⁻¹ ^ d Z : ℝ)) : ℂ) * phi0 ψ ν hZ h (fun q => f (sig Z t⁻¹ q)) p := by
  obtain ⟨x, v⟩ := p
  have hx : x ∈ Bz Z := hp.1
  have hDy : D Z (x - Pr Z x) = 0 := D_sub_Pr hZ h x
  have hPy : Pr Z (x - Pr Z x) = 0 := Pr_of_D hZ h hDy
  have hpi : piZ Z x = x - Pr Z x := piZ_eq_sub hZ h hx
  have hsig : (sig Z t (x, v)) = (x - Pr Z x + (t : k) • Pr Z x, v) := by
    simp only [sig, hpi, sub_sub_cancel]
  rw [hsig, characteristic_function_integral_apply, characteristic_function_integral_apply]
  have hP : Pr Z (x - Pr Z x + (t : k) • Pr Z x) = (t : k) • Pr Z x := by
    rw [Pr_add, hPy, Pr_smul, show Pr Z (Pr Z x) = Pr Z x from Pr_E hZ h _, zero_add]
  have hD : D Z (x - Pr Z x + (t : k) • Pr Z x) = (t : k) • D Z x := by
    rw [D_add, hDy, D_smul, D_Pr hZ h, zero_add]
  simp only [hP, hD, add_sub_cancel_right]
  have hyB : ∀ u, x - Pr Z x + E Z u ∈ Bz Z := fun u =>
    (BzL Z).add_mem ((BzL Z).sub_mem hx (Pr_mem x).1) (E_mem Z u).1
  have hpi2 : ∀ u, piZ Z (x - Pr Z x + E Z u) = x - Pr Z x := fun u => by
    rw [piZ_eq_sub hZ h (hyB u), Pr_add, hPy, Pr_E hZ h, zero_add, add_sub_cancel_right]
  have hs : ∀ u, sig Z t⁻¹ (x - Pr Z x + E Z u, v) = (x - Pr Z x + E Z ((t⁻¹ : k) • u), v) := fun u => by
    simp only [sig, hpi2, add_sub_cancel_left, E_smul, Units.val_inv_eq_inv_val]
  simp only [hs]
  have key := GlobalTheory.WeilM.integral_comp_mulVec ν (Tu (Z := Z) t)
    (fun u => f (x - Pr Z x + E Z ((t⁻¹ : k) • u), v) * (ψ (u ⬝ᵥ D Z x) : ℂ))
  have ht : (t : k) ≠ 0 := t.ne_zero
  simp only [Tu_mulVec, Tu_det, map_pow, smul_smul, inv_mul_cancel₀ ht, one_smul, smul_dotProduct,
    ← dotProduct_smul] at key
  rw [← key]
  have hn : (nabs k t : ℝ) = ((distribHaarChar k t : NNReal) : ℝ) := rfl
  have hpos : (nabs k t : ℝ) ≠ 0 := by rw [hn]; exact_mod_cast (distribHaarChar_pos).ne'
  rw [NNReal.coe_pow, ← hn]
  push_cast
  have hposC : ((nabs k t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos
  rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hposC, one_pow, one_mul]

end PositivityTheory.RgUd.T.Nil.Four.Phi2
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.ReflH

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.RgUd.T.Nil.Four.Phi2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

def ReflH (hZ : CR Z) (h : Hyp Z) : Sp k n ≃ₜ Sp k n where
  toFun := Refl (Z := Z)
  invFun := Refl (Z := Z)
  left_inv := Refl_Refl hZ h
  right_inv := Refl_Refl hZ h
  continuous_toFun := by
    show Continuous fun p : Sp k n => (p.1 - (2 : k) • Pr Z p.1, p.2)
    exact (continuous_fst.sub (((continuous_Pr Z).comp continuous_fst).const_smul (2 : k))).prodMk continuous_snd
  continuous_invFun := by
    show Continuous fun p : Sp k n => (p.1 - (2 : k) • Pr Z p.1, p.2)
    exact (continuous_fst.sub (((continuous_Pr Z).comp continuous_fst).const_smul (2 : k))).prodMk continuous_snd

theorem d_eq [CharZero k] (hZ : CR Z) : d Z = dB0 Z := by
  classical
  have hsurj : LinearMap.range ((qL Z).domRestrict (BzL Z)) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨c, hc, rfl⟩ := PositivityTheory.RgUd.T.Nil.Four.Alg.qZ_surj hZ y
    exact ⟨⟨c, Z_le_Bz Z hZ hc⟩, rfl⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker ((qL Z).domRestrict (BzL Z))
  rw [hsurj, finrank_top, Module.finrank_fin_fun] at hrn
  have hker : LinearMap.ker ((qL Z).domRestrict (BzL Z)) = (B0 Z).comap (BzL Z).subtype := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply, Submodule.mem_comap,
      Submodule.subtype_apply, B0, Submodule.mem_inf, x.2, true_and]
  have e : Module.finrank k (LinearMap.ker ((qL Z).domRestrict (BzL Z))) =
      Module.finrank k (B0 Z) := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe (inf_le_left : B0 Z ≤ BzL Z)).finrank_eq
  have hS : Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) =
      BzL Z := by
    ext x
    rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
    rfl
  have hC : Module.finrank k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) =
      Module.finrank k (BzL Z) := by
    rw [← Subalgebra.finrank_toSubmodule, hS]
  show Module.finrank k (B0 Z) = Module.finrank k _ - Module.finrank k _
  rw [hC]
  omega

theorem phiP [CharZero k] : PhiP (k := k) := by
  intro n Z hZ
  borelize k
  have h : Hyp Z := ⟨PositivityTheory.RgUd.T.Nil.Four.Alg.piZ_mem hZ, PositivityTheory.RgUd.T.Nil.Four.Alg.qZ_piZ hZ,
    fun x c hc hq => PositivityTheory.RgUd.T.Nil.Four.Alg.piZ_eq hZ hc hq,
    fun w hw hb => PositivityTheory.RgUd.T.Nil.Four.Alg.trB_nondeg hZ hw hb⟩
  obtain ⟨ψ, hψ⟩ := exists_hasConductor_one k
  let ν : Measure k := Measure.addHaar
  have hcomp : ∀ (U : Set (Sp k n)) (e : Sp k n ≃ₜ Sp k n), (∀ x, e x ∈ U → x ∈ U) →
      ∀ f : Sp k n → ℂ, f ∈ supportedIn U → (fun p => f (e p)) ∈ supportedIn U := by
    intro U e he f hf
    rw [mem_supportedIn, GroundTheory.Automorphic.mem_locallyConstantCompactSupport] at hf ⊢
    obtain ⟨⟨hlc, hcs⟩, hsu⟩ := hf
    refine ⟨⟨hlc.comp_continuous e.continuous, hcs.comp_homeomorph e⟩, ?_⟩
    intro x hx
    exact he x (hsu hx)
  have hU : ∀ (e : Sp k n ≃ₜ Sp k n) (f : Sp k n → ℂ), f ∈ supportedIn (Set.univ : Set (Sp k n)) →
      (fun p => f (e p)) ∈ supportedIn (Set.univ : Set (Sp k n)) :=
    fun e => hcomp Set.univ e (fun _ _ => Set.mem_univ _)
  have hRf : ∀ f : Sp k n → ℂ, f ∈ supportedIn (Set.univ : Set (Sp k n)) →
      (fun p => f (Refl (Z := Z) p)) ∈ supportedIn (Set.univ : Set (Sp k n)) :=
    fun f hf => hU (ReflH hZ h) f hf
  have hRU : ∀ f : Sp k n → ℂ, f ∈ supportedIn (UU : Set (Sp k n)) →
      (fun p => f (Refl (Z := Z) p)) ∈ supportedIn (UU : Set (Sp k n)) :=
    fun f hf => hcomp UU (ReflH hZ h) (fun _ hx => hx) f hf
  obtain ⟨q, hq⟩ := (supportedIn (Set.univ : Set (Sp k n))).exists_isCompl
  let Φ : (Sp k n → ℂ) →ₗ[ℂ] Sp k n → ℂ :=
    (phiS ψ ν hZ h hψ.continuous).comp ((supportedIn (Set.univ : Set (Sp k n))).projectionOnto q hq)
  have hΦ : ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), Φ f = phi0 ψ ν hZ h f := by
    intro f hf
    have e1 : (supportedIn (Set.univ : Set (Sp k n))).projectionOnto q hq f = ⟨f, hf⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hq ⟨f, hf⟩
    simp only [Φ, LinearMap.comp_apply, e1]
    rfl
  let κ : ℂ := (((distribHaarChar k (GeneralLinearGroup.det (Gu hZ h)) : NNReal) : ℝ) : ℂ)⁻¹ *
    (((ν.real (𝒪[k] : Set k) ^ 2 * nabs k 1) ^ d Z : ℝ) : ℂ)
  have hχ : (distribHaarChar k (GeneralLinearGroup.det (Gu hZ h)) : NNReal) ≠ 0 := by
    have e2 := map_mul_eq_one (distribHaarChar k)
      (mul_inv_cancel (GeneralLinearGroup.det (Gu hZ h)))
    exact left_ne_zero_of_mul_eq_one e2
  have hO : IsOpen ((𝒪[k] : Set k)) := (ValuativeRel.valuation k).isOpen_integer
  have hC : IsCompact ((𝒪[k] : Set k)) :=
    isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace 𝒪[k])
  have hν : 0 < ν.real (𝒪[k] : Set k) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hO.measure_ne_zero ν ⟨0, zero_mem _⟩) hC.measure_lt_top.ne
  have hn1 : nabs k 1 = 1 := by
    simp [nabs]
  have hκ : κ ≠ 0 := by
    refine mul_ne_zero (inv_ne_zero ?_) ?_
    · exact_mod_cast hχ
    · rw [hn1, mul_one]
      exact_mod_cast pow_ne_zero _ (pow_pos hν 2).ne'
  let Φ' : (Sp k n → ℂ) →ₗ[ℂ] Sp k n → ℂ :=
    κ⁻¹ • (Φ.comp (LinearMap.funLeft ℂ ℂ (Refl (Z := Z))))
  have hΦ' : ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)),
      Φ' f = κ⁻¹ • phi0 ψ ν hZ h (fun p => f (Refl (Z := Z) p)) := by
    intro f hf
    show κ⁻¹ • Φ (fun p => f (Refl (Z := Z) p)) = _
    rw [hΦ _ (hRf f hf)]
  refine ⟨Φ, Φ', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf
    rw [hΦ f hf]
    exact test_vector_mem_schwartz_bruhat ψ ν hZ h hψ hf
  · intro f hf
    rw [hΦ' f hf]
    exact Submodule.smul_mem _ _ (test_vector_mem_schwartz_bruhat ψ ν hZ h hψ (hRf f hf))
  · intro f hf y hy p hp
    rw [hΦ f hf]
    exact fourier_transform_vanishes_on_fibre ψ ν hZ h f hy hp
  · intro g hg f hf p hp
    have hA : (fun p => f (act g p)) ∈ supportedIn (Set.univ : Set (Sp k n)) :=
      hU (PositivityTheory.RgUd.T.Nil.Four.Alg.actH g) f hf
    rw [hΦ f hf, hΦ _ hA]
    exact fourier_transform_equivariant ψ ν hZ h hg f p
  · intro f hf
    have hf' := supportedIn_mono (Set.subset_univ _) hf
    rw [hΦ f hf']
    exact fourier_transform_preserves_compact ψ ν hZ h hψ hf
  · intro f hf
    have hf' := supportedIn_mono (Set.subset_univ _) hf
    rw [hΦ' f hf']
    exact Submodule.smul_mem _ _ (fourier_transform_preserves_compact ψ ν hZ h hψ (hRU f hf))
  · intro f hf p hp
    have hR := hRf f hf
    have hm := test_vector_mem_schwartz_bruhat ψ ν hZ h hψ hR
    rw [hΦ' f hf, map_smul, hΦ _ hm, Pi.smul_apply, fourier_transform_involution ψ ν hZ h hψ hR p,
      Refl_Refl hZ h, smul_eq_mul, ← mul_assoc]
    change κ⁻¹ * κ * f p = f p
    rw [inv_mul_cancel₀ hκ, one_mul]
  · intro t f hf p hp
    have hS : (fun p => f (sig Z t⁻¹ p)) ∈ supportedIn (Set.univ : Set (Sp k n)) :=
      hU (PositivityTheory.RgUd.T.Nil.Four.Alg.sigH hZ t⁻¹) f hf
    rw [hΦ f hf, hΦ _ hS, ← d_eq hZ]
    exact fourier_transform_scaling ψ ν hZ h t f hp

end PositivityTheory.RgUd.T.Nil.Four.Phi2
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.SuppCongr

section

@[expose] public section

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Four

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem supp_congr {n : ℕ} {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ}
    (h : Supp ξ (Bz Z ×ˢ Set.univ)) {f g : Sp k n → ℂ} (hf : f ∈ supportedIn (Set.univ : Set (Sp k n)))
    (hg : g ∈ supportedIn (Set.univ : Set (Sp k n))) (e : ∀ p ∈ Bz Z ×ˢ Set.univ, f p = g p) : ξ f = ξ g := by
  have := h (f - g) ((supportedIn Set.univ).sub_mem hf hg) fun p hp => by simp [e p hp]
  rwa [map_sub, sub_eq_zero] at this

theorem fourP_of (hΦ : PhiP (k := k)) (hC : CompP (k := k)) : FourP (k := k) := by
  intro n Z hZ
  obtain ⟨Φ, Φ', h1, h2, h3, h4, h5, h6, h7, h8⟩ := hΦ n Z hZ
  obtain ⟨hCs, hCa, -, -⟩ := hC n Z hZ
  have hUU : ∀ f ∈ supportedIn (UU : Set (Sp k n)), f ∈ supportedIn (Set.univ : Set (Sp k n)) :=
    fun f hf => ⟨hf.1, Set.subset_univ _⟩
  let F : ((Sp k n → ℂ) →ₗ[ℂ] ℂ) →ₗ[ℂ] (Sp k n → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun ξ => ξ ∘ₗ Φ
      map_add' := fun a b => by ext; simp
      map_smul' := fun a b => by ext; simp }
  have hF : ∀ ξ f, F ξ f = ξ (Φ f) := fun _ _ => rfl
  refine ⟨F, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ξ hξ f hf hz
    rw [hF]
    refine hξ _ (h1 f hf) fun p hp => ?_
    have hpF : p ∈ Fib Z (qZ Z p.1) := ⟨⟨hp.1, rfl⟩, Set.mem_univ _⟩
    exact h3 f hf (qZ Z p.1) (fun q hq => hz q ⟨hq.1.1, Set.mem_univ _⟩) p hpF
  · intro ξ y hξ f hf hz
    rw [hF]
    exact hξ _ (h1 f hf) (h3 f hf y hz)
  · intro ξ hξ hinv g hg f hf
    rw [hF, hF]
    have hfg : (fun q => f (act g q)) ∈ supportedIn (Set.univ : Set (Sp k n)) := hCa g f hf
    rw [supp_congr hξ (h1 _ hfg) (hCa g _ (h1 f hf)) (fun p hp => h4 g hg f hf p hp)]
    exact hinv g hg _ (h1 f hf)
  · intro ξ hξ
    constructor
    · intro hk f hf
      rw [hF]
      exact hk _ (h5 f hf)
    · intro hk f hf
      have hfu := hUU f hf
      rw [← supp_congr hξ (h1 _ (h2 f hfu)) hfu (fun p hp => h7 f hfu p hp)]
      exact hk _ (h6 f hf)
  · intro ξ hξ f hf
    rw [hF]
    exact hξ _ (h1 f hf)
  · intro t ξ hξ f hf
    rw [hF]
    show ξ (fun q => Φ f (sig Z t q)) = _ * ξ (Φ (fun q => f (sig Z t⁻¹ q)))
    have hsf : (fun q => f (sig Z t⁻¹ q)) ∈ supportedIn (Set.univ : Set (Sp k n)) := hCs t⁻¹ f hf
    rw [← smul_eq_mul, ← map_smul]
    exact supp_congr hξ (hCs t _ (h1 f hf)) (Submodule.smul_mem _ _ (h1 _ hsf))
      (fun p hp => by rw [Pi.smul_apply, smul_eq_mul]; exact h8 t f hf p hp)

end PositivityTheory.RgUd.T.Nil.Four
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.FourP

section

@[expose] public section

namespace PositivityTheory.RgUd.T.Nil.Four.Final

open PositivityTheory.RgUd.T.Nil

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem fourP [CharZero k] : FourP (k := k) :=
  PositivityTheory.RgUd.T.Nil.Four.fourP_of PositivityTheory.RgUd.T.Nil.Four.Phi2.phiP PositivityTheory.RgUd.T.Nil.Four.Alg.compP

theorem locQ : LocQ (k := k) := PositivityTheory.RgUd.T.Nil.Four.locQ_pf

end PositivityTheory.RgUd.T.Nil.Four.Final
end
end
