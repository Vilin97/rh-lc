module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.Chl
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharPolEqOfDegNeZero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisRestrictionWdCompatible
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemWeilGroupAtPlaceOfFixesExtension
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RestrictsLpDimMono0CharPol
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeaklyAttachedGaloisRepresentationBaseChangeRest
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.ValLeOneOfIsIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.FrobeniusCharpolyOfUnlinkedUnramifiedSupport
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamEqUnramifiedSatakeOfFrobenius

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU

theorem wdOf_eq_satWD_of_frobEig : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G E Ω →* GL (Fin n) (Qbar l)), Continuous r → ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ B : Multiset ℂˣ, UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat n (normV w) B) → wdOf h hl ι r = satWD h n B := by
  intro Ω _ E _ _ _ _ l _ ι n r _hr w hl A h B hF
  obtain ⟨hI, hFr⟩ := hF A h
  have ht := isTameChar_tameL h hl
  have hN : IsMonodromy (tameL h hl) r 0 :=
    (isMonodromy_zero_iff (h := h)).mpr (.of_trivial fun σ => hI σ σ.2)
  have hu1 : (wdOf h hl ι r).unr := (hN.unr_wdOf_iff hl ht ι).mpr hI
  have hm : (0 : ℂ) ∉ B.map fun b => ((b⁻¹ : ℂˣ) : ℂ) := by
    simp
  have hs := WD.lpUnr_spec (h := h) _ hm
  have hu2 : (satWD h n B).unr := (WD.unr_tw _ _).mpr hs.1
  rw [WD.unr_eq_lpUnr _ hu1, WD.unr_eq_lpUnr _ hu2]
  congr 1
  rw [satWD, WD.frobEig_tw _ _ hs.1, hs.2.1, WD.frobEig, WD.eig, hN.charPol_wdOf hl ht ι (frob h)]
  have hσ : IsFrob A (normV w) ((frob h : Weil h) : G E Ω) := deg_eq_one_iff.mp deg_frob
  have hc := Formalism.L2.NR.charpoly_map_of_inv ι.toRingHom (r (frob h : G E Ω)) _
    (by rw [← map_inv]; exact hFr _ hσ)
  have e : ∀ s : Multiset ℂ, s.map (fun μ => X - C μ⁻¹) = (s.map (·⁻¹)).map (fun a => X - C a) := fun s => by
    rw [Multiset.map_map]; rfl
  rw [hc, e, roots_multiset_prod_X_sub_C, UpperTheory.V.Af.algSat, Multiset.map_map, Multiset.map_map]
  have hB : (do let a ← B; pure (a : ℂ) : Multiset ℂ) = B.map (Units.val : ℂˣ → ℂ) := by
    simp [Multiset.bind_singleton]
  rw [hB, Multiset.map_map]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_inv_eq_inv_val]
  have hq : (0 : ℝ) ≤ ((normV w : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow hq, show (1 - (n : ℝ)) / 2 = -(((n : ℝ) - 1) / 2) by ring,
    Real.rpow_neg hq, Complex.ofReal_inv, mul_inv, mul_comm]

end GlobalTheory.RoadU
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamEqUnramifiedSatakeOfFrobeniusStatement

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.weilDeligneParam_eq_unramifiedSatake_of_frobenius : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G E Ω →* GL (Fin n) (Qbar l)), Continuous r → ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ B : Multiset ℂˣ, UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat n (normV w) B) → wdOf h hl ι r = satWD h n B := by
  first | (exact @GlobalTheory.RoadU.wdOf_eq_satWD_of_frobEig) | (exact GlobalTheory.RoadU.wdOf_eq_satWD_of_frobEig) | (intros; apply GlobalTheory.RoadU.wdOf_eq_satWD_of_frobEig  <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.ToralGalois2

section

@[expose] public section

open GlobalTheory.RoadU

namespace GalTw
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem toralGal_of_holds : UpperTheory.Gal.ToralGalois.Inq → SphericalLevelCondition .all .unr → ToralGal := by
  intro hI hS E Ω _ _ _ _ _ _ l _ ι n hn π χ hπ r hr w hl A h σ hσ ξ hξ hsupp hunl a ha
  have key : ∀ g : Weil h, deg g ≠ 0 →
      (wdOf h hl ι r).mono0 ∧ (wdOf h hl ι r).charPol g = ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
    intro g hg
    obtain ⟨M, _, _, _, _, _, _, _, u, h', P, χ', hP, hlift, hfix, B, hB, hchar⟩ :=
      GlobalTheory.T.frobenius_charpoly_of_unlinked_unramified_support hI Ω E l ι n hn π χ hπ r hr w A h σ hσ ξ hξ hsupp hunl a ha g hg
    have hl' : ((l : ℕ) : 𝓞 M) ∉ u.asIdeal := by
      intro hm
      apply hl
      rw [← h]
      rw [← h'] at hm
      simpa using hm
    have hr' : Weak P ι (resTo M r) := GlobalTheory.GalCut.weak_comp_res E M Ω l ι n π P hlift r hr
    have hF : UpperTheory.V.Af.FrobEig ι (resTo M r) u (UpperTheory.V.Af.algSat n (normV u) B) :=
      hS M Ω l ι n hn P χ' hP (resTo M r) hr' u trivial B hB hl'
    have hwd : wdOf h' hl' ι (resTo M r) = satWD h' n B :=
      GlobalTheory.T.weilDeligneParam_eq_unramifiedSatake_of_frobenius Ω M l ι n (resTo M r) hr'.1 u hl' A h' B hF
    have hres := GlobalTheory.AboveL.wdOf_restricts E M Ω A w u h h' l ι n r hl hl' hr.1
    obtain ⟨-, hmono, hcp⟩ := GlobalTheory.AboveL.restricts_lpDim_mono0_charPol E M Ω A w u h h' _ _ hres
    let g' : G M Ω := AlgEquiv.ofRingEquiv (f := (g : G E Ω).toRingEquiv) hfix
    have hmem : g' ∈ Weil h' := GlobalTheory.AboveL.mem_weil_of_fix E M Ω A w u h h' g g' fun _ => rfl
    refine ⟨hmono.mp ?_, ?_⟩
    · rw [hwd]
      simp [satWD, WD.lpUnr]
    · rw [← hcp g ⟨g', hmem⟩ fun _ => rfl, hwd]
      exact hchar g ⟨g', hmem⟩ fun _ => rfl
  have hy : ∀ g : Weil h, (WD.mk (WDRep.ofChars h (fun j : Fin n => (ξ j).comp a) fun j => ha.smooth (hξ j))).charPol g =
      ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
    intro g
    rw [WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
    rfl
  refine ⟨(key (frob h) (by rw [deg_frob]; exact one_ne_zero)).1, fun g => ?_⟩
  rw [← hy g]
  exact GlobalTheory.AboveL.charPol_eq_of_deg_ne_zero E Ω A w h _ _ (fun g hg => (key g hg).2.trans (hy g).symm) g

end GlobalTheory.RoadU

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end
end GalTw
end
end
