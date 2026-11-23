module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.IsInvForm
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.HighestDerivativeProducts.HighestDerivProd
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.BernOf
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.FrobeniusReciprocity.LocStep
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.DerivPos
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.ThmA
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.IsClosedGzS
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.TraceForm
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.Imports
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.IsClosedGzS
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.TraceForm
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.TranslInv
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseOrbits.MainE
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseOrbits.OneDim
import GroundTheory.AutomorphicForms.WhittakerDistribution
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
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.BezoutHypotheses.ContinuousHom
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AddCharConductorIntegersContinuousNeOneStatement
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.TraceEqZeroOfQZ
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.HaarFourierSupport.FourierTransformTranslationInvariant
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.EInjective
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.HaarFourierSupport.DistribHaarCharAdU
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.FibreQuotientHolds
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.QuasiOrbits.OrbQ
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.TraceForm
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.BaseVanishing.VanOf

section

section

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.TP.Nil.Base

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.BasePf PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem van_of {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (h0 : dB0 Z = 0) : Van Z := by
  intro ξ hS hI
  have : TotallyDisconnectedSpace k := totallyDisconnectedSpace_localField
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) k) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → k))
  have : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  have : T2Space (Matrix (Fin n) (Fin n) k) := inferInstanceAs (T2Space (Fin n → Fin n → k))
  intro f hf
  have hle : supportedIn {p : Sp k n | p.2 ≠ 0} ≤ LinearMap.ker ξ := supportedIn_le_of_local fun p hp => by
    obtain ⟨e, he, hee, hev, hprim⟩ := prim Z hZ.1 hZ.2 p.2 hp
    refine ⟨{q : Sp k n | e *ᵥ q.2 ≠ 0}, ?_, hev, fun g hg =>
      LinearMap.mem_ker.2 (mainE Z hZ h0 e he hee hprim p.2 hev ξ hS hI g hg)⟩
    exact isOpen_ne_fun (continuous_const.matrix_mulVec continuous_snd) continuous_const
  exact LinearMap.mem_ker.1 (hle hf)

theorem baseQ : BaseQ k := by
  intro n Z hZ h0 ξ hS hI
  refine van_of k Z hZ h0 ξ (fun f hf hf0 => hS f hf fun p hp => hf0 p ⟨hp.1.1, hp.2⟩) hI

end PositivityTheory.RgUd.TP.Nil.Base

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.HaarFourierSupport.SuppCongr

section

section

noncomputable section

set_option linter.unusedSectionVars false

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.RgUd.TP.Nil.Four

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem supp_congr' {C : Set (Sp k n)} {ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (h : Supp ξ C) {f g : Sp k n → ℂ}
    (hf : f ∈ supportedIn (Set.univ : Set (Sp k n))) (hg : g ∈ supportedIn (Set.univ : Set (Sp k n)))
    (e : ∀ p ∈ C, f p = g p) : ξ f = ξ g := by
  have := h (f - g) ((supportedIn Set.univ).sub_mem hf hg) fun p hp => by simp [e p hp]
  rwa [map_sub, sub_eq_zero] at this

def homH (t : kˣ) : Sp k n ≃ₜ Sp k n where
  toFun := PositivityTheory.RgUd.TP.Nil.hom t
  invFun := PositivityTheory.RgUd.TP.Nil.hom t⁻¹
  left_inv p := by
    simp [PositivityTheory.RgUd.TP.Nil.hom, smul_smul]
  right_inv p := by
    simp [PositivityTheory.RgUd.TP.Nil.hom, smul_smul]
  continuous_toFun := (continuous_fst.const_smul ((t : kˣ) : k)).prodMk continuous_snd
  continuous_invFun := (continuous_fst.const_smul ((t⁻¹ : kˣ) : k)).prodMk continuous_snd

def trH (z : Matrix (Fin n) (Fin n) k) : Sp k n ≃ₜ Sp k n where
  toFun p := (p.1 + z, p.2)
  invFun p := (p.1 - z, p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := (continuous_fst.add continuous_const).prodMk continuous_snd
  continuous_invFun := (continuous_fst.sub continuous_const).prodMk continuous_snd

variable (k) in
theorem fourQ : FourQ k := by
  intro hT n Z hZ
  obtain ⟨τ, hs, hnd, hnil⟩ := hT n Z hZ
  have h : Hyp τ Z := ⟨hs, hnd, hnil⟩
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  obtain ⟨ψ, hψ⟩ := GlobalTheory.SplitWeil.exists_hasConductor_one (k := k)
  have hψc : Continuous ψ := (GlobalTheory.T.addChar_conductor_integers_continuous_ne_one k ψ hψ).1
  let ν : Measure k := Measure.addHaar
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (supportedIn (Set.univ : Set (Sp k n)))
  let Φ : (Sp k n → ℂ) →ₗ[ℂ] (Sp k n → ℂ) := LinearMap.ofIsCompl hC (phiS ψ ν h hψc) 0
  have hΦ : ∀ f (hf : f ∈ supportedIn (Set.univ : Set (Sp k n))), Φ f = phi0 ψ ν h f := fun f hf =>
    LinearMap.ofIsCompl_left_apply hC (⟨f, hf⟩ : supportedIn (Set.univ : Set (Sp k n)))
  have h1 : ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), Φ f ∈ supportedIn (Set.univ : Set (Sp k n)) :=
    fun f hf => by rw [hΦ f hf]; exact test_vector_mem_schwartz_bruhat ψ ν h hψ hf
  set K : ℂ := ((distribHaarChar k (Matrix.GeneralLinearGroup.det (Gu h)) : ℝ) : ℂ)⁻¹ *
    ((((ν.real (𝒪[k] : Set k) ^ 2 * nabs k 1) ^ (dd Z) : ℝ)) : ℂ) with hKdef
  have hK : K ≠ 0 := by
    have h1 : 0 < ν.real (𝒪[k] : Set k) :=
      ENNReal.toReal_pos ((isOpen_int k).measure_ne_zero ν ⟨0, zero_mem _⟩) (isCompact_int k).measure_lt_top.ne
    have h2 : 0 < nabs k 1 := by
      show (0 : ℝ) < ((distribHaarChar k 1 : NNReal) : ℝ)
      exact_mod_cast distribHaarChar_pos
    have h3 : ((distribHaarChar k (Matrix.GeneralLinearGroup.det (Gu h)) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (distribHaarChar_pos).ne'
    refine mul_ne_zero (inv_ne_zero h3) ?_
    exact_mod_cast (pow_pos (mul_pos (pow_pos h1 2) h2) _).ne'
  let Φ' : (Sp k n → ℂ) →ₗ[ℂ] (Sp k n → ℂ) := K⁻¹ • (Φ ∘ₗ LinearMap.funLeft ℂ ℂ (Refl τ Z))
  have hR : ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), (fun q => f (Refl τ Z q)) ∈
      supportedIn (Set.univ : Set (Sp k n)) := fun f hf => by
    have := PositivityTheory.RgUd.T.Nil.Four.Alg.comp_mem hf
      { toFun := Refl τ Z, invFun := Refl τ Z, left_inv := Refl_Refl h, right_inv := Refl_Refl h,
        continuous_toFun := (continuous_fst.sub (((continuous_Pr τ Z).comp continuous_fst).const_smul (2 : k))).prodMk
          continuous_snd
        continuous_invFun := (continuous_fst.sub (((continuous_Pr τ Z).comp continuous_fst).const_smul (2 : k))).prodMk
          continuous_snd : Sp k n ≃ₜ Sp k n }
    exact this
  have hRU : ∀ f ∈ supportedIn (UU : Set (Sp k n)), (fun q => f (Refl τ Z q)) ∈ supportedIn (UU : Set (Sp k n)) :=
    fun f hf => ⟨(hR f ⟨hf.1, Set.subset_univ _⟩).1, fun q hq => by
      have := hf.2 (show Refl τ Z q ∈ Function.support f from hq)
      exact this⟩
  have h1' : ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), Φ' f ∈ supportedIn (Set.univ : Set (Sp k n)) := by
    intro f hf
    show K⁻¹ • Φ (fun q => f (Refl τ Z q)) ∈ _
    refine Submodule.smul_mem _ _ ?_
    exact h1 _ (hR f hf)
  have hU : ∀ f ∈ supportedIn (UU : Set (Sp k n)), Φ f ∈ supportedIn (UU : Set (Sp k n)) := by
    intro f hf
    rw [hΦ f ⟨hf.1, Set.subset_univ _⟩]
    exact fourier_transform_preserves_compact ψ ν h hψ hf
  have hU' : ∀ f ∈ supportedIn (UU : Set (Sp k n)), Φ' f ∈ supportedIn (UU : Set (Sp k n)) := by
    intro f hf
    show K⁻¹ • Φ (fun q => f (Refl τ Z q)) ∈ _
    refine Submodule.smul_mem _ _ ?_
    exact hU _ (hRU f hf)
  have hinv : ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), ∀ p, Φ (Φ' f) p = f p := by
    intro f hf p
    show Φ (K⁻¹ • Φ (fun q => f (Refl τ Z q))) p = f p
    rw [map_smul, hΦ _ (hR f hf), hΦ _ (test_vector_mem_schwartz_bruhat ψ ν h hψ (hR f hf)), Pi.smul_apply,
      fourier_transform_involution ψ ν h hψ (hR f hf), Refl_Refl h, ← hKdef, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hK,
      one_mul]
  have cs : ∀ (s : kˣ) (g : Sp k n → ℂ), g ∈ supportedIn (Set.univ : Set (Sp k n)) →
      (fun q => g (PositivityTheory.RgUd.TP.Nil.hom s q)) ∈ supportedIn (Set.univ : Set (Sp k n)) := fun s g hg => by
    have := PositivityTheory.RgUd.T.Nil.Four.Alg.comp_mem hg (homH s)
    exact this
  let 𝓕 : ((Sp k n → ℂ) →ₗ[ℂ] ℂ) →ₗ[ℂ] ((Sp k n → ℂ) →ₗ[ℂ] ℂ) :=
    { toFun := fun ξ => ξ ∘ₗ Φ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨𝓕, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ξ hξ f hf h0
    refine hξ _ (h1 f hf) fun p hp => ?_
    rw [hΦ f hf]
    exact fourier_transform_support ψ ν h f h0 hp
  · intro ξ hξ hi g hg f hf
    have ca : (fun q => f (act g q)) ∈ supportedIn (Set.univ : Set (Sp k n)) := by
      have := PositivityTheory.RgUd.T.Nil.Four.Alg.comp_mem hf (PositivityTheory.RgUd.T.Nil.Four.Alg.actH g)
      exact this
    have ca' : (fun q => Φ f (act g q)) ∈ supportedIn (Set.univ : Set (Sp k n)) := by
      have := PositivityTheory.RgUd.T.Nil.Four.Alg.comp_mem (h1 f hf) (PositivityTheory.RgUd.T.Nil.Four.Alg.actH g)
      exact this
    show ξ (Φ fun q => f (act g q)) = ξ (Φ f)
    refine (supp_congr' hξ (h1 _ ca) ca' fun p hp => ?_).trans (hi g hg _ (h1 f hf))
    rw [hΦ _ ca, hΦ f hf]
    exact fourier_transform_equivariant ψ ν h hg f hp.1
  · intro ξ hξ
    constructor
    · intro hk f hf
      exact hk _ (hU f hf)
    · intro hk f hf
      have hf' : f ∈ supportedIn (Set.univ : Set (Sp k n)) := supportedIn_mono (Set.subset_univ _) hf
      rw [← supp_congr' hξ (h1 _ (h1' f hf')) hf' fun p _ => hinv f hf' p]
      exact hk _ (hU' f hf)
  · intro ξ h0 f hf
    exact h0 _ (h1 f hf)
  · intro t ξ hξ f hf
    have hc1 := cs t _ (h1 f hf)
    have hc2 : ((((nabs k t)⁻¹ ^ dB Z : ℝ)) : ℂ) • Φ (fun q => f (PositivityTheory.RgUd.TP.Nil.hom t⁻¹ q)) ∈
        supportedIn (Set.univ : Set (Sp k n)) :=
      (supportedIn Set.univ).smul_mem _ (h1 _ (cs t⁻¹ f hf))
    have e := supp_congr' hξ hc1 hc2 fun p hp => by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hΦ f hf, hΦ _ (cs t⁻¹ f hf), fourier_transform_homothety ψ ν h t f hp.1, dd_eq]
    change ξ (fun q => Φ f (PositivityTheory.RgUd.TP.Nil.hom t q)) = _ * ξ (Φ fun q => f (PositivityTheory.RgUd.TP.Nil.hom t⁻¹ q))
    rw [e, map_smul, smul_eq_mul]
  · intro ξ hξ z hz f hf
    have ct : (fun p : Sp k n => f (p.1 + z, p.2)) ∈ supportedIn (Set.univ : Set (Sp k n)) := by
      have := PositivityTheory.RgUd.T.Nil.Four.Alg.comp_mem hf (trH z)
      exact this
    show ξ (Φ fun p => f (p.1 + z, p.2)) = ξ (Φ f)
    refine supp_congr' hξ (h1 _ ct) (h1 f hf) fun p hp => ?_
    obtain ⟨x, v⟩ := p
    obtain ⟨⟨hxB, hxn⟩, -⟩ := hp
    rw [hΦ _ ct, hΦ f hf]
    refine fourier_transform_translation_invariant ψ ν h hZ f hz hxB ?_ v
    exact h.nil _ ⟨mul_mem_Bz Z (PositivityTheory.RgUd.T.Nil.Four.Phi2.Z_le_Bz Z hZ hz) hxB,
      Commute.isNilpotent_mul_left (hxB z hz) hxn⟩

end PositivityTheory.RgUd.TP.Nil.Four
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.NilCore

section

section

namespace PositivityTheory.RgUd.TP.Nil.Final

open PositivityTheory.RgUd.TP

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nilCore (hT : TraceForm k) (hU : PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k)) : NilCore k :=
  PositivityTheory.RgUd.TP.Nil.Asm.nilCore_of k (PositivityTheory.RgUd.TP.Nil.Four.fourQ k) (PositivityTheory.RgUd.TP.Nil.Orb.orbQ k)
    (PositivityTheory.RgUd.TP.Nil.Fib2.fibQ k) (PositivityTheory.RgUd.TP.Nil.Base.baseQ k) hT hU

end PositivityTheory.RgUd.TP.Nil.Final
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.TraceFormAlt

section

@[expose] public section

namespace PositivityTheory.RgUd.TP.Final

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem traceForm : TraceForm k := Loc.Final.traceForm k
theorem unimod : TraceForm k → PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k) := Loc.Final.unimod k
theorem desc (p : ℕ) [Fact p.Prime] [CharP k p] : PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k) → Desc k := PositivityTheory.RgUd.TP.Desc.Final.desc k p
theorem locOff : LocOff k := Loc.Final.locOff k
theorem locAll : LocAll k := Loc.Final.locAll k
theorem transl : Transl k := Loc.Final.transl k
theorem nilCore :
    TraceForm k → PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k) → NilCore k := Nil.Final.nilCore k

theorem van_of (hD : Desc k) (h1 : LocOff k) (h2 : LocAll k) (h3 : Transl k) (h4 : NilCore k) :
    ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → Van Z := by
  obtain ⟨μ, hμ⟩ := hD
  suffices h : ∀ (m n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), μ n Z = m → CR Z → Van Z from
    fun n Z hZ => h _ n Z rfl hZ
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n Z hm hZ
    have hP : ∀ χ : Polynomial k, ∃ (r : ℕ) (F : Fin r → Set (Matrix (Fin n) (Fin n) k)), IsPieces Z χ F ∧ ∀ i,
        (∃ c ∈ Z, ∀ x ∈ F i, IsNilpotent (x - c)) ∨ FibVan Z (F i) := fun χ => by
      obtain ⟨r, F, hF, hi⟩ := hμ n Z hZ χ
      exact ⟨r, F, hF, fun i => (hi i).imp_right fun h => h fun n' Z' hZ' hlt => ih _ (hm ▸ hlt) n' Z' rfl hZ'⟩
    have hN := h4 n Z hZ (h1 n Z hZ hP)
    refine h2 n Z hZ fun χ => ?_
    obtain ⟨r, F, hF, hi⟩ := hP χ
    exact ⟨r, F, hF, fun i => (hi i).elim (fun ⟨c, hc, hx⟩ => h3 n Z hZ hN c hc _ (hF.1 i).2.1 hx) id⟩

theorem thmT (p : ℕ) [Fact p.Prime] [CharP k p] : PositivityTheory.RgUd.ThmT k := by
  intro n Z hcomm hred ξ hsupp hinv f hf
  have hU := unimod k (traceForm k)
  exact van_of k (desc k p hU) (locOff k) (locAll k) (transl k) (nilCore k (traceForm k) hU) n Z ⟨hcomm, hred⟩ ξ
    (fun g hg h0 => hsupp g hg fun p hp => h0 p ⟨hp, Set.mem_univ _⟩) (fun g hg f hf => hinv g hg f hf) f hf

end PositivityTheory.RgUd.TP.Final
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.BernAll

section

@[expose] public section

namespace PositivityTheory.RgUd.All

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem thmT : ThmT k := by
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with h | rfl
  · haveI : Fact p.Prime := ⟨h⟩
    exact TP.Final.thmT k p
  · haveI : CharZero k := CharP.charP_to_charZero k
    exact T.Final.thmT k

theorem thmB : ThmB k := AB.Final.thmB k (AB.Final.thmA k (thmT k))

theorem bernAt : BernAt k :=
  Prod.Final.bern_of k (Form.U.Final.derivTop k (thmB k)) (Form.U.Final.derivPos k (thmB k))
    (GlobalTheory.RgGu.Leib.Hand.leibnizOrd k)

theorem bernsteinUnitaryProductIrreducible : GlobalTheory.Published.BernsteinUnitaryProductIrreducible := fun k _ _ _ _ => bernAt k

end PositivityTheory.RgUd.All
end
end
