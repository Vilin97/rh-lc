module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.MirSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicWhittakerEquivariantBumpMirabolicStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovSemilocalSmoothBumpStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAutomorphicFormFixedOfLocallyIntegralFixedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaCellsDisjointOffFinset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSphericalWhittakerTorusElementNeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CondExpEqZeroOfNotMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaledLocalCharacterUnitConductorConductorExponeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalWhittakerDiagonalShiftRamifiedCharacterStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerMulTorusShiftAddEqSphericalProduct

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun
open scoped Classical

namespace GlobalTheory.RamShift

theorem whittaker_torusShift_add_factorisation_induction (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (T : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E (m + 1))
    (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ)
    (hα : ∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w))) (φ) (hφV : φ ∈ π.V)
    (hφ : ∀ w ∉ T, ∀ k ∈ KGL w (n := (m + 1)), act (.fin (locGL E (m + 1) w k)) φ = φ)
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (hϖ : ∀ w, IsUnifV E w (ϖ w : w.adicCompletion E))
    (x : GA E (m + 1)) (hx : x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) T) (L : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ)) :
    (∀ w ∈ T, L w = 0) → (∀ w, 0 ≤ L w (Fin.last m)) →
      GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ ((shift m T ϖ).1 + L)) =
        GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ (shift m T ϖ).1) *
          ∏ w ∈ L.support, (if h : w ∈ T then 1 else
            GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) (L w)) := by
  induction L using Finsupp.induction with
  | zero => intro _ _; simp
  | single_add a b f ha hb ih =>
    intro hT hlast
    have hfa : f a = 0 := Finsupp.notMem_support_iff.1 ha
    have haT : a ∉ T := fun h => hb (by simpa [hfa] using hT a h)
    have hfT : ∀ w ∈ T, f w = 0 := fun w hw => by
      have hne : a ≠ w := fun e => haT (e ▸ hw)
      simpa [Finsupp.single_apply, hne] using hT w hw
    have hflast : ∀ w, 0 ≤ f w (Fin.last m) := fun w => by
      by_cases hw : a = w
      · subst hw; simp [hfa]
      · simpa [Finsupp.single_apply, hw] using hlast w
    have hblast : 0 ≤ b (Fin.last m) := by simpa [hfa] using hlast a
    set l₀ := (shift m T ϖ).1 with hl₀
    have hsplit : l₀ + (Finsupp.single a b + f) =
        (l₀ - Finsupp.single a (l₀ a) + f) + Finsupp.single a (l₀ a + b) := by
      ext w i
      by_cases hw : a = w
      · subst hw; simp [hfa]
      · simp [Finsupp.single_apply, hw]
    have hjoin : (l₀ - Finsupp.single a (l₀ a) + f) + Finsupp.single a (l₀ a) = l₀ + f := by
      ext w i
      by_cases hw : a = w
      · subst hw; simp [hfa]
      · simp [Finsupp.single_apply, hw]
    set g := x * GlobalTheory.CellDec.tl (m + 1) ϖ (l₀ - Finsupp.single a (l₀ a) + f) with hg
    have hga : GeneralLinearGroup.map ((pLoc E a).comp (pFin E)) g = 1 := by
      change GlobalTheory.CellDec.compV E (m + 1) a g = 1
      rw [hg, map_mul, GlobalTheory.CellDec.compV_tl]
      have h0 : (l₀ - Finsupp.single a (l₀ a) + f) a = 0 := by simp [hfa]
      have hxa : GlobalTheory.CellDec.compV E (m + 1) a x = 1 := hx a haT
      rw [h0, hxa, GlobalTheory.IwaCell.tD_zero, one_mul]
    have hl₀a : l₀ a = fun i : Fin (m + 1) => condExp ϖ a * ((m : ℤ) - ((i : ℕ) : ℤ)) :=
      shift_apply_of_notMem m ϖ haT
    have key := GlobalTheory.T.sphericalWhittaker_diagonalShift_ramifiedCharacter E m π a (α ⟨a, haT⟩) (hα ⟨a, haT⟩) φ hφV (hφ a haT) (ϖ a) (hϖ a) (condExp ϖ a)
      (GlobalTheory.T.scaledLocalCharacter_unitConductor_conductorExponent E ϖ a (hϖ a)) g hga b hblast
    have h1 : l₀ a + b = fun i : Fin (m + 1) => condExp ϖ a * ((m : ℤ) - ((i : ℕ) : ℤ)) + b i := by
      rw [hl₀a]; rfl
    rw [hsplit, GlobalTheory.CellDec.tl_add, GlobalTheory.CellDec.tl_single, ← mul_assoc, ← hg, h1, key, ← hl₀a,
      ← GlobalTheory.CellDec.tl_single, hg, mul_assoc, ← GlobalTheory.CellDec.tl_add, hjoin, ih hfT hflast,
      Finsupp.support_single_add ha hb, Finset.prod_cons, dite_eq_right haT]
    have hval : (Finsupp.single a b + f) a = b := by simp [hfa]
    have hrest : ∏ w ∈ f.support, (if h : w ∈ T then 1 else
          GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) ((Finsupp.single a b + f) w)) =
        ∏ w ∈ f.support, (if h : w ∈ T then 1 else
          GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) (f w)) := by
      refine Finset.prod_congr rfl fun w hw => ?_
      have hne : a ≠ w := fun e => ha (e ▸ hw)
      simp [Finsupp.single_apply, hne]
    rw [hval, hrest]
    change GlobalTheory.RSCell.sphZ (Ideal.absNorm a.asIdeal) _ b * _ = _
    ring

theorem whit_mul_tl_shift_add : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (π : CuspSub E (m + 1)) (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ),
    (∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w))) →
    ∀ φ ∈ π.V, (∀ w ∉ T, ∀ k ∈ KGL w (n := (m + 1)), act (.fin (locGL E (m + 1) w k)) φ = φ) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) T, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, 0 ≤ l.1 w (Fin.last m)) →
      GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ ((GlobalTheory.RamShift.shift m T ϖ).1 + l.1)) =
        GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ (GlobalTheory.RamShift.shift m T ϖ).1) *
          ∏ w ∈ l.1.support, (if h : w ∈ T then 1 else
            GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) (l.1 w)) := by
  intro E _ _ _ m T π α hα φ hφV hφ ϖ hϖ x hx l hl
  exact whittaker_torusShift_add_factorisation_induction E m T π α hα φ hφV hφ ϖ hϖ x hx l.1 l.2 hl

end GlobalTheory.RamShift
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerMulTorusShiftAddEqSphericalProductStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun
open scoped Classical

theorem _root_.GlobalTheory.T.whittaker_mul_torusShift_add_eq_sphericalProduct : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (π : CuspSub E (m + 1)) (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ),
    (∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w))) →
    ∀ φ ∈ π.V, (∀ w ∉ T, ∀ k ∈ KGL w (n := (m + 1)), act (.fin (locGL E (m + 1) w k)) φ = φ) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) T, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, 0 ≤ l.1 w (Fin.last m)) →
      GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ ((GlobalTheory.RamShift.shift m T ϖ).1 + l.1)) =
        GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ (GlobalTheory.RamShift.shift m T ϖ).1) *
          ∏ w ∈ l.1.support, (if h : w ∈ T then 1 else
            GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) (l.1 w)) := by
  first | exact @GlobalTheory.RamShift.whit_mul_tl_shift_add | exact GlobalTheory.RamShift.whit_mul_tl_shift_add | (intros; apply GlobalTheory.RamShift.whit_mul_tl_shift_add <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsShiftedVectorShintaniFormulaRamified

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

namespace GlobalTheory.RamShift

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

theorem eq_finGL_of_pInf {q : GA E n} (hq : GeneralLinearGroup.map (pInf E) q = 1) :
    q = finGL E n (GeneralLinearGroup.map (pFin E) q) := by
  have h := infGL_mul_finGL q
  rw [hq, map_one, one_mul] at h
  exact h.symm

theorem pInf_tl (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) :
    GeneralLinearGroup.map (pInf E) (GlobalTheory.CellDec.tl n ϖ l) = 1 := by
  unfold GlobalTheory.CellDec.tl
  exact pInf_finGL _

theorem compV_tl_of_eq_zero (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) {v : HeightOneSpectrum (𝓞 E)} (hv : l v = 0) :
    GlobalTheory.CellDec.compV E n v (GlobalTheory.CellDec.tl n ϖ l) = 1 := by
  rw [GlobalTheory.CellDec.compV_tl, hv, GlobalTheory.IwaCell.tD_zero]

theorem one_mem_mirS (S : Finset (HeightOneSpectrum (𝓞 E))) (m : ℕ) : (1 : GA E (m + 1)) ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) := by
  refine ⟨fun w _ => map_one _, fun j => ?_⟩
  rw [Units.val_one, Matrix.one_apply]
  by_cases h : j = Fin.last m
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]

theorem mem_NA_of_mem {u : GA E n} (hu : u ∈ GlobalTheory.JSW.NA (E := E) (a := n)) : u ∈ GlobalTheory.CellDec.NA E n :=
  (GlobalTheory.SmGL.mem_unipB (Ad E)).2 ⟨fun i j hij => hu.1 i j hij, hu.2⟩

end GlobalTheory.RamShift


open GlobalTheory.RamShift in
theorem GlobalTheory.RamShift.exists_shifted_bump_shintani : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (π : CuspSub E (m + 1)), π.IsUnitary → ∀ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ),
    (∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w))) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∃ F ∈ GlobalTheory.JSW.mspanR π, ∃ l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, l₀.1 w (Fin.last m) = 0) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧
      (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
        (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, F (g * k) = F g) ∧
      GlobalTheory.JSW.whit F (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 ∧
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) T ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m),
        GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 → ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * p ∈ C) ∧
      ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) T ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, 0 ≤ l.1 w (Fin.last m)) →
        GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ (l₀.1 + l.1)) = GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) *
          ∏ w ∈ l.1.support, (if h : w ∈ T then 1 else
            GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) (l.1 w)) := by
  intro E _ _ _ m T π _ α hα ϖ hϖ
  set l₀ := shift m T ϖ with hl₀
  set t₀ := GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 with ht₀def
  have ht₀inf : GeneralLinearGroup.map (pInf E) t₀ = 1 := pInf_tl ϖ l₀.1
  set D := GeneralLinearGroup.map (pFin E) t₀ with hD
  have ht₀ : t₀ = finGL E (m + 1) D := eq_finGL_of_pInf ht₀inf
  obtain ⟨b, hb1, hbN, hbC, hbU, hbS⟩ := GlobalTheory.T.exists_adelic_whittaker_equivariant_bump_mirabolic E m T
  obtain ⟨φ, hφV, hφK, x₀, hx₀, hW₀⟩ := GlobalTheory.T.exists_spherical_whittaker_torusElement_ne_zero E m T π α hα ϖ hϖ
  set φ' := act (.fin D) φ with hφ'def
  have hφ'V : φ' ∈ π.V := π.stable _ φ hφV
  have hφ' : ∀ g, φ'.1 g = φ.1 (g * t₀) := fun g => by rw [ht₀]; rfl
  have hWφ' : ∀ y, whit φ'.1 y = whit φ.1 (y * t₀) := fun y => by
    rw [whit_mul_right]
    congr 1
    funext z
    exact hφ' z
  obtain ⟨F₀, hF₀V, hF₀b, hF₀U, hF₀inv, hF₀rel⟩ :=
    GlobalTheory.T.kirillov_semilocal_smooth_bump E m T b hbN hbC hbU hbS π φ' hφ'V ⟨x₀, hx₀, by rw [hWφ']; exact hW₀⟩
  have hWF : ∀ y, whit (fun g => F₀ (g * t₀⁻¹)) y = whit F₀ (y * t₀⁻¹) := fun y =>
    (whit_mul_right F₀ y t₀⁻¹).symm
  refine ⟨fun g => F₀ (g * t₀⁻¹), mspanR_rt hF₀V _, l₀, fun w => shift_last m T ϖ w, ?_, ?_, ?_, ?_, ?_⟩
  ·
    obtain ⟨U, hUo, hU⟩ := hF₀U
    refine ⟨U.comap (MulAut.conj D).toMonoidHom, ?_, fun u hu g => ?_⟩
    · exact hUo.preimage ((continuous_const.mul continuous_id).mul continuous_const)
    · have e : g * finGL E (m + 1) u * t₀⁻¹ = g * t₀⁻¹ * finGL E (m + 1) (D * u * D⁻¹) := by
        rw [ht₀, map_mul, map_mul, map_inv]; group
      show F₀ (g * finGL E (m + 1) u * t₀⁻¹) = F₀ (g * t₀⁻¹)
      rw [e]
      exact hU _ hu _
  ·
    intro k hk hkinf hkT g
    have hkf := eq_finGL_of_pInf hkinf
    set kf := GeneralLinearGroup.map (pFin E) k with hkfdef
    have hφk : act (.fin kf) φ = φ := GlobalTheory.T.smoothAutomorphicForm_fixed_of_locally_integral_fixed E (m + 1) φ (π.cusp φ hφV).1 T hφK kf
      (fun w hw => by
        have := GlobalTheory.CellDec.mem_US.1 hk w hw
        exact this)
      (fun w hw => hkT w hw)
    have e : g * k * t₀⁻¹ = g * t₀⁻¹ * (t₀ * k * t₀⁻¹) := by group
    show F₀ (g * k * t₀⁻¹) = F₀ (g * t₀⁻¹)
    rw [e]
    refine hF₀inv _ ?_ ?_ ?_ _
    · rw [map_mul, map_mul, map_inv, ht₀inf, hkinf]; simp
    · intro w hw
      change GlobalTheory.CellDec.compV E (m + 1) w (t₀ * k * t₀⁻¹) = 1
      rw [map_mul, map_mul, map_inv, compV_tl_of_eq_zero ϖ l₀.1 (l₀.2 w hw), hkT w hw]; simp
    · intro y
      rw [hφ', hφ']
      have e2 : y * (t₀ * k * t₀⁻¹) * t₀ = y * t₀ * finGL E (m + 1) kf := by rw [← hkf]; group
      rw [e2]
      exact congrArg (fun ψ : Sm E (m + 1) => ψ.1 (y * t₀)) hφk
  ·
    rw [hWF, mul_inv_cancel, hF₀b 1 (one_mem_mirS T m), hb1]
    exact one_ne_zero
  ·
    obtain ⟨C, hC, hCp⟩ := hbC
    refine ⟨C, hC, fun p hp hne => ?_⟩
    rw [hWF, mul_inv_cancel_right, hF₀b p hp] at hne
    obtain ⟨u, hu, hup⟩ := hCp p hp hne
    exact ⟨u⁻¹, inv_mem (mem_NA_of_mem hu), hup⟩
  ·
    intro p hp l hl
    have hcomm : GlobalTheory.CellDec.tl (m + 1) ϖ (l₀.1 + l.1) = GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * t₀ := by
      rw [add_comm l₀.1 l.1, GlobalTheory.CellDec.tl_add]
    rw [hWF, hWF, hcomm, ← mul_assoc, mul_inv_cancel_right, mul_inv_cancel_right]
    rw [hF₀rel (GlobalTheory.CellDec.tl (m + 1) ϖ l.1) _ (pInf_tl ϖ l.1)
      (fun w hw => compV_tl_of_eq_zero ϖ l.1 (l.2 w hw)) (fun x hx => ?_) p hp.1, mul_comm]
    rw [hWφ', hWφ', mul_assoc, ← GlobalTheory.CellDec.tl_add, add_comm l.1 l₀.1, GlobalTheory.T.whittaker_mul_torusShift_add_eq_sphericalProduct E m T π α hα φ hφV hφK ϖ hϖ x hx l hl, mul_comm]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsShiftedVectorShintaniFormulaRamifiedStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.exists_shifted_vector_shintani_formula_ramified : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (π : CuspSub E (m + 1)), π.IsUnitary → ∀ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ),
    (∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w))) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∃ F ∈ GlobalTheory.JSW.mspanR π, ∃ l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, l₀.1 w (Fin.last m) = 0) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧
      (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
        (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, F (g * k) = F g) ∧
      GlobalTheory.JSW.whit F (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 ∧
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) T ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m),
        GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 → ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * p ∈ C) ∧
      ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) T ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, 0 ≤ l.1 w (Fin.last m)) →
        GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ (l₀.1 + l.1)) = GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) *
          ∏ w ∈ l.1.support, (if h : w ∈ T then 1 else
            GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) (l.1 w)) := by
  first
  | exact @GlobalTheory.RamShift.exists_shifted_bump_shintani
  | exact GlobalTheory.RamShift.exists_shifted_bump_shintani
  | (intros; apply GlobalTheory.RamShift.exists_shifted_bump_shintani <;> assumption)
end
end
