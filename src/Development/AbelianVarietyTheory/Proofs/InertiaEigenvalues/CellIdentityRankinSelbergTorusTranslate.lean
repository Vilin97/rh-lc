module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
public import Development.AbelianVarietyTheory.Definitions.Divisors.MirSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMirabolicWhittakerReductionCellStatement
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddHaarMapMulFiniteIdeleOfUniformizerPowers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowDiagonalMulMemLatticeIffStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowSubSingleNotMemLatticeOfNegExponentStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumPairsEq
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdeleModuleDetDiagonalUniformiserMul

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

namespace GlobalTheory.CellDec.DetMod

theorem prod_adl {E : Type} [Field E] [NumberField E] {ι : Type} (s : Finset ι)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (m : ι → HeightOneSpectrum (𝓞 E) →₀ ℤ) :
    ∏ i ∈ s, GlobalTheory.CellDec.adl ϖ (m i) = GlobalTheory.CellDec.adl ϖ (∑ i ∈ s, m i) := by
  induction s using Finset.induction_on with
  | empty => simp [GlobalTheory.CellDec.adl_zero]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, GlobalTheory.CellDec.adl_add]

theorem det_finGL' {E : Type} [Field E] [NumberField E] {a : ℕ} (k : GL (Fin a) (Af E)) :
    GeneralLinearGroup.det (finGL E a k) = finId E (GeneralLinearGroup.det k) := by
  let p : Ad E →+* InfiniteAdeleRing E := RingHom.fst (InfiniteAdeleRing E) (Af E)
  refine Units.ext (Prod.ext ?_ ?_)
  · have h := GlobalTheory.CuspRep.det_map p (finGL E a k)
    have h0 : GeneralLinearGroup.map p (finGL E a k) = 1 :=
      map_cornerGL_of_zero (sFin E) p (fun x => rfl) k
    rw [h0, map_one, Units.val_one] at h
    change p _ = _
    rw [← h]
    change (1 : InfiniteAdeleRing E) = (1 : InfiniteAdeleRing E) - 0 + 0
    simp
  · have h := GlobalTheory.CuspRep.det_map (pFin E) (finGL E a k)
    have h0 : GeneralLinearGroup.map (pFin E) (finGL E a k) = GeneralLinearGroup.map (RingHom.id _) k :=
      map_cornerGL_of_hom (sFin E) (pFin E) (RingHom.id _) (fun x => rfl) k
    rw [h0] at h
    change pFin E _ = _
    rw [← h]
    change _ = (1 : Af E) - 1 + (GeneralLinearGroup.det k : (Af E)ˣ)
    rw [sub_self, zero_add]
    rfl

end GlobalTheory.CellDec.DetMod

theorem GlobalTheory.CellDec.DetMod.ideleModule_det_tl_mul : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ),
    (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (g : GA E n),
      (ideleModule E (GeneralLinearGroup.det (GlobalTheory.CellDec.tl n ϖ l * g)) : ℝ) =
        (∏ v ∈ l.support, ((qV E v : ℝ) ^ (∑ i, l v i))⁻¹) * (ideleModule E (GeneralLinearGroup.det g) : ℝ) := by
  intro E _ _ n ϖ hϖ l g
  rw [map_mul, map_mul, Positive.val_mul]
  congr 1
  have hdet : GeneralLinearGroup.det (GlobalTheory.SmGL.diagT (Af E) (Fin n)
      fun i => GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l)) =
      ∏ i, GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, GlobalTheory.SmGL.val_diagT, Matrix.det_diagonal, Units.coe_prod]
  unfold GlobalTheory.CellDec.tl
  rw [GlobalTheory.CellDec.DetMod.det_finGL', hdet, GlobalTheory.CellDec.DetMod.prod_adl]
  rw [GlobalTheory.AdeleScale.ideleModule_finId_adl ϖ hϖ _ l.support]
  · refine Finset.prod_congr rfl fun v _ => ?_
    congr 2
    rw [Finsupp.finsetSum_apply]
    rfl
  · intro v hv
    rw [Finsupp.notMem_support_iff] at hv
    rw [Finsupp.finsetSum_apply]
    simp [hv]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdeleModuleDetDiagonalUniformiserMulStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.ideleModule_det_diagonalUniformiser_mul : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ),
    (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (g : GA E n),
      (ideleModule E (GeneralLinearGroup.det (GlobalTheory.CellDec.tl n ϖ l * g)) : ℝ) =
        (∏ v ∈ l.support, ((qV E v : ℝ) ^ (∑ i, l v i))⁻¹) * (ideleModule E (GeneralLinearGroup.det g) : ℝ) := by
  first | exact @GlobalTheory.CellDec.DetMod.ideleModule_det_tl_mul | exact GlobalTheory.CellDec.DetMod.ideleModule_det_tl_mul | (intros; apply GlobalTheory.CellDec.DetMod.ideleModule_det_tl_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalLocalFactorNormSq

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

namespace GlobalTheory.RSCell

theorem wtS_eq_sum (N : ℕ) (a : Fin N → ℤ) :
    GlobalTheory.CellDec.wtS N a = ∑ i : Fin N, ((N : ℤ) - 1 - 2 * ((i : ℕ) : ℤ)) * a i := by
  first
  | exact @_root_.GlobalTheory.WeightSumSplit.wtS_eq
  | exact _root_.GlobalTheory.WeightSumSplit.wtS_eq
  | (apply _root_.GlobalTheory.WeightSumSplit.wtS_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.WeightSumSplit.wtS_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.WeightSumSplit.wtS_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.WeightSumSplit.wtS_eq ..)

theorem locFac_eq_wtS_sphZ : ∀ (q : ℕ), 0 < q → ∀ (n : ℕ) (α : Fin (n + 1) → ℂ) (x : ℝ) (ν : Fin (n + 1) → ℤ), 0 ≤ ν (Fin.last n) →
    ENNReal.ofReal ((q : ℝ) ^ GlobalTheory.CellDec.wtS (n + 1) ν) * ENNReal.ofReal ((q : ℝ) ^ (-((∑ i, (ν i : ℝ)) * x))) *
      ‖GlobalTheory.RSCell.sphZ q α ν‖ₑ ^ 2 = GlobalTheory.RSCell.locFac q α x ν := by
  intro q hq n α x ν hlast
  by_cases hA : Antitone ν
  · have hnn : ∀ i, 0 ≤ ν i := fun i => le_trans hlast (hA (Fin.le_last i))
    have hAn : Antitone (fun i => (ν i).toNat) := fun i j h => Int.toNat_le_toNat (hA h)
    rw [GlobalTheory.RSCell.locFac, if_pos ⟨hA, hnn⟩, GlobalTheory.RSCell.sphZ, if_pos hA, GlobalTheory.JSW.sphW, if_pos hAn]
    set s := GlobalTheory.JSW.schurAt (fun i => (ν i).toNat) α
    set w : ℤ := GlobalTheory.CellDec.wtS (n + 1) ν with hw
    have hc : (∑ i : Fin (n + 1), ((((n + 1 : ℕ)) : ℂ) - 1 - 2 * ((i : ℕ) : ℂ)) * (((ν i).toNat : ℕ) : ℂ)) = ((w : ℤ) : ℂ) := by
      rw [hw, wtS_eq_sum]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (((ν i).toNat : ℕ) : ℂ) = ((ν i : ℤ) : ℂ) by exact_mod_cast Int.toNat_of_nonneg (hnn i)]
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hsum : (((∑ i, (ν i).toNat : ℕ)) : ℝ) = ∑ i, (ν i : ℝ) := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      exact_mod_cast Int.toNat_of_nonneg (hnn i)
    rw [hc, hsum]
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (zpow_nonneg hq'.le _), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hq]
    have hre : (-((w : ℂ)) / 2).re = -(w : ℝ) / 2 := by simp
    rw [hre, mul_pow, ← Real.rpow_natCast ((q : ℝ) ^ (-(w : ℝ) / 2)), ← Real.rpow_mul hq'.le,
      ← Real.rpow_intCast]
    have h1 : (q : ℝ) ^ (w : ℝ) * (q : ℝ) ^ (-(w : ℝ) / 2 * ((2 : ℕ) : ℝ)) = 1 := by
      rw [← Real.rpow_add hq']
      norm_num
    calc (q : ℝ) ^ (w : ℝ) * (q : ℝ) ^ (-((∑ i, (ν i : ℝ)) * x)) *
          ((q : ℝ) ^ (-(w : ℝ) / 2 * ((2 : ℕ) : ℝ)) * ‖s‖ ^ 2)
        = ((q : ℝ) ^ (w : ℝ) * (q : ℝ) ^ (-(w : ℝ) / 2 * ((2 : ℕ) : ℝ))) * (‖s‖ ^ 2 * (q : ℝ) ^ (-((∑ i, (ν i : ℝ)) * x))) := by ring
      _ = _ := by rw [h1, one_mul]
  · rw [GlobalTheory.RSCell.locFac, if_neg (fun h => hA h.1), GlobalTheory.RSCell.sphZ, if_neg hA]
    simp

end GlobalTheory.RSCell
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalLocalFactorNormSqStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.spherical_local_factor_norm_sq : ∀ (q : ℕ), 0 < q → ∀ (n : ℕ) (α : Fin (n + 1) → ℂ) (x : ℝ) (ν : Fin (n + 1) → ℤ), 0 ≤ ν (Fin.last n) →
    ENNReal.ofReal ((q : ℝ) ^ GlobalTheory.CellDec.wtS (n + 1) ν) * ENNReal.ofReal ((q : ℝ) ^ (-((∑ i, (ν i : ℝ)) * x))) *
      ‖GlobalTheory.RSCell.sphZ q α ν‖ₑ ^ 2 = GlobalTheory.RSCell.locFac q α x ν := by
  first | exact @GlobalTheory.RSCell.locFac_eq_wtS_sphZ | exact GlobalTheory.RSCell.locFac_eq_wtS_sphZ | (intros; apply GlobalTheory.RSCell.locFac_eq_wtS_sphZ <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellIdentityRankinSelbergTorusTranslate

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.CellPw

variable {E : Type} [Field E] [NumberField E]

theorem rowInf_tl [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (g : GA E n) (r : Fin n) :
    (fun i => pInf E ((GlobalTheory.CellDec.tl n ϖ l * g).val r i)) = fun i => pInf E (g.val r i) := by
  have h : GeneralLinearGroup.map (pInf E) (GlobalTheory.CellDec.tl n ϖ l * g) = GeneralLinearGroup.map (pInf E) g := by
    rw [map_mul, GlobalTheory.CellDec.tl, pInf_finGL, one_mul]
  funext i
  exact congrArg (fun M : GL (Fin n) (Cinf E) => M.val r i) h

theorem bInt_of_not_mem [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (ℓ : Fin a) (F : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (x : ℝ) (h : GA E a)
    (hm : (fun i => pFin E (h.val ℓ i)) - η ∉ GlobalTheory.ThetaPoisson.latt a J) :
    GlobalTheory.RSCell.bInt ℓ F Φ J η x h = 0 := by
  simp [GlobalTheory.RSCell.bInt, GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, Set.indicator_of_notMem hm]

theorem bInt_of_mem [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (ℓ : Fin a) (F : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (x : ℝ) (h : GA E a)
    (hm : (fun i => pFin E (h.val ℓ i)) - η ∈ GlobalTheory.ThetaPoisson.latt a J) :
    GlobalTheory.RSCell.bInt ℓ F Φ J η x h =
      ENNReal.ofReal (‖GlobalTheory.JSW.whit F (h * (infGL E a (GlobalTheory.RSTheta.rowGL ℓ (fun i => pInf E (h.val ℓ i))))⁻¹)‖ ^ 2 *
        ‖Φ (fun i => pInf E (h.val ℓ i))‖ * (ideleModule E (GeneralLinearGroup.det h) : ℝ) ^ x) := by
  rw [GlobalTheory.RSCell.bInt, GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, GlobalTheory.RSTheta.rsInf, Set.indicator_of_mem hm,
    ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  congr 1
  simp only [Pi.one_apply, mul_one, norm_mul, Complex.norm_conj]
  ring

theorem prod_supp_add {n : ℕ} (q : HeightOneSpectrum (𝓞 E) → ℝ) (hq : ∀ v, q v ≠ 0) (f : (Fin n → ℤ) →+ ℤ)
    (a b : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) :
    ∏ v ∈ (a + b).support, q v ^ f ((a + b) v) =
      (∏ v ∈ a.support, q v ^ f (a v)) * ∏ v ∈ b.support, q v ^ f (b v) := by
  have := Finsupp.prod_add_index' (f := a) (g := b) (h := fun v y => q v ^ f y) (fun v => by simp)
    (fun v y₁ y₂ => by simp [zpow_add₀ (hq v)])
  simpa [Finsupp.prod] using this

def wtSHom (n : ℕ) : (Fin n → ℤ) →+ ℤ where
  toFun := GlobalTheory.CellDec.wtS n
  map_zero' := by simp [GlobalTheory.CellDec.wtS]
  map_add' a b := by
    simp only [GlobalTheory.CellDec.wtS, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp <;> ring

def negSumHom (n : ℕ) : (Fin n → ℤ) →+ ℤ where
  toFun a := -∑ i, a i
  map_zero' := by simp
  map_add' a b := by simp [Finset.sum_add_distrib]; ring


omit [Field E] [NumberField E] in
theorem cell_identity : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂ) (F : GA E (m + 1) → ℂ) (l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T)
      (U : Subgroup (GL (Fin (m + 1)) (Af E))) (Φ : (Fin (m + 1) → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
    (∀ w, l₀.1 w (Fin.last m) = 0) → (∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g) →
    (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g) →
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) T ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, 0 ≤ l.1 w (Fin.last m)) →
      GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ (l₀.1 + l.1)) = GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) *
        ∏ w ∈ l.1.support, (if h : w ∈ T then 1 else GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (α ⟨w, h⟩) (l.1 w))) →
    tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) → (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    (∀ y : Fin (m + 1) → Af E, y - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ κ ∈ U, (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
        ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
          pLoc E w (y j)) →
    ∀ (x : ℝ), ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T,
      ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) * GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) =
        ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) * GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * g) *
          GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) := by
  intro E _ _ _ m T ϖ hϖ α F l₀ U Φ J hl₀ hU hK hN hprof hΦ hJ horb x g hg l
  have hνT : ∀ v ∈ T, (l.1 - l₀.1) v = 0 := fun v hv => by simp [l.2 v hv, l₀.2 v hv]
  let ν : GlobalTheory.CellDec.abelian₂ E (m + 1) T := ⟨l.1 - l₀.1, hνT⟩
  have hνl : l₀.1 + ν.1 = l.1 := by simp [ν]
  have hνw : ∀ w, ν.1 w (Fin.last m) = l.1 w (Fin.last m) := fun w => by simp [ν, hl₀ w]
  by_cases hneg : ∃ w, l.1 w (Fin.last m) < 0
  · obtain ⟨w, hw⟩ := hneg
    have hwT : w ∉ T := fun h => by simp [l.2 w h] at hw
    rw [bInt_of_not_mem _ _ _ _ _ _ _ (GlobalTheory.T.lastRow_sub_single_not_mem_lattice_of_neg_exponent E m T ϖ hϖ J hJ g hg l w hw)]
    have h2 : GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) = 0 := by
      refine Finset.prod_eq_zero (i := w) ?_ ?_
      · rw [Finsupp.mem_support_iff]
        intro h
        have := congrFun h (Fin.last m)
        simp [hl₀ w] at this
        omega
      · rw [dite_eq_right hwT]
        exact GlobalTheory.RSCell.locFac_of_neg _ _ _ (i := Fin.last m) (by simp [hl₀ w]; exact hw)
    rw [h2]
    simp
  push_neg at hneg
  have hl₀n : ∀ w, 0 ≤ l₀.1 w (Fin.last m) := fun w => (hl₀ w).ge
  have hposl := GlobalTheory.T.lastRow_diagonal_mul_mem_lattice_iff E m T ϖ hϖ J hJ g hg l hneg
  have hposl₀ := GlobalTheory.T.lastRow_diagonal_mul_mem_lattice_iff E m T ϖ hϖ J hJ g hg l₀ hl₀n
  by_cases hI : (fun i => pFin E (g.val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J
  swap
  · rw [bInt_of_not_mem _ _ _ _ _ _ _ (fun h => hI (hposl.1 h)),
      bInt_of_not_mem _ _ _ _ _ _ _ (fun h => hI (hposl₀.1 h))]
    simp
  rw [bInt_of_mem _ _ _ _ _ _ _ (hposl.2 hI), bInt_of_mem _ _ _ _ _ _ _ (hposl₀.2 hI),
    rowInf_tl, rowInf_tl]
  set u : Fin (m + 1) → Cinf E := fun i => pInf E (g.val (Fin.last m) i) with hu
  by_cases hΦu : Φ u = 0
  · simp [hΦu]
  have hunit : IsUnit (pInf E (g.val (Fin.last m) (Fin.last m))) :=
    GlobalTheory.RSTheta.isUnit_of_mem_rowSet (hΦ (subset_tsupport _ hΦu))
  obtain ⟨p, hp, hpl⟩ := GlobalTheory.T.exists_mirabolic_whittaker_reduction_cell E m T ϖ F U J hU hK hN horb g hg hunit hI
  rw [hpl l, hpl l₀, GlobalTheory.T.ideleModule_det_diagonalUniformiser_mul E (m + 1) ϖ hϖ l.1 g, GlobalTheory.T.ideleModule_det_diagonalUniformiser_mul E (m + 1) ϖ hϖ l₀.1 g]
  have hpr := hprof p hp ν (fun w => by rw [hνw]; exact hneg w)
  rw [hνl] at hpr
  rw [hpr]

  have hq : ∀ v : HeightOneSpectrum (𝓞 E), (qV E v : ℝ) ≠ 0 := fun v => by
    rw [qV, Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hqpos : ∀ v : HeightOneSpectrum (𝓞 E), 0 < (qV E v : ℝ) := fun v =>
    lt_of_le_of_ne (Nat.cast_nonneg _) (hq v).symm
  have hcell : GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) = ENNReal.ofReal (∏ w ∈ ν.1.support,
      ((qV E w : ℝ) ^ GlobalTheory.CellDec.wtS (m + 1) (ν.1 w) * (qV E w : ℝ) ^ (-((∑ i, (ν.1 w i : ℝ)) * x)) *
        ‖(if h : w ∈ T then 1 else GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (α ⟨w, h⟩) (ν.1 w))‖ ^ 2)) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun w _ => by positivity)]
    refine Finset.prod_congr rfl fun w hw => ?_
    have hwT : w ∉ T := fun h => (Finsupp.mem_support_iff.1 hw) (hνT w h)
    rw [dite_eq_right hwT, dite_eq_right hwT, ← GlobalTheory.T.spherical_local_factor_norm_sq (Ideal.absNorm w.asIdeal) (Nat.pos_of_ne_zero (by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot)) m (α ⟨w, hwT⟩) x (ν.1 w) (by rw [hνw]; exact hneg w),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm_eq_enorm]
    rfl
  have hd0 : ∀ k : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ), 0 ≤ GlobalTheory.CellDec.dinv (m + 1) k := fun k =>
    Finset.prod_nonneg fun v _ => (zpow_pos (hqpos v) _).le
  rw [hcell, ← ENNReal.ofReal_mul (hd0 _), ← ENNReal.ofReal_mul (hd0 _), ← ENNReal.ofReal_mul (mul_nonneg (hd0 _) <| mul_nonneg (mul_nonneg (by positivity) (norm_nonneg _))
    (Real.rpow_nonneg (mul_nonneg (Finset.prod_nonneg fun v _ => (inv_pos.2 (zpow_pos (hqpos v) _)).le)
      ((ideleModule E (GeneralLinearGroup.det g)).2.le)) _))]
  congr 1
  have hd : GlobalTheory.CellDec.dinv (m + 1) l.1 = GlobalTheory.CellDec.dinv (m + 1) l₀.1 *
      ∏ w ∈ ν.1.support, (qV E w : ℝ) ^ GlobalTheory.CellDec.wtS (m + 1) (ν.1 w) := by
    rw [← hνl]
    exact prod_supp_add (fun v => (qV E v : ℝ)) hq (wtSHom (m + 1)) l₀.1 ν.1
  have hQ : ∀ k : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ),
      ∏ v ∈ k.support, ((qV E v : ℝ) ^ ∑ i, k v i)⁻¹ = ∏ v ∈ k.support, (qV E v : ℝ) ^ negSumHom (m + 1) (k v) := by
    intro k
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← _root_.zpow_neg]; rfl
  have hQl : ∏ v ∈ l.1.support, ((qV E v : ℝ) ^ ∑ i, l.1 v i)⁻¹ =
      (∏ v ∈ l₀.1.support, ((qV E v : ℝ) ^ ∑ i, l₀.1 v i)⁻¹) * ∏ v ∈ ν.1.support, ((qV E v : ℝ) ^ ∑ i, ν.1 v i)⁻¹ := by
    rw [hQ, hQ, hQ, ← hνl]
    exact prod_supp_add (fun v => (qV E v : ℝ)) hq (negSumHom (m + 1)) l₀.1 ν.1
  have hQν : (∏ v ∈ ν.1.support, ((qV E v : ℝ) ^ ∑ i, ν.1 v i)⁻¹) ^ x =
      ∏ v ∈ ν.1.support, (qV E v : ℝ) ^ (-((∑ i, (ν.1 v i : ℝ)) * x)) := by
    have hprod : ∀ s : Finset (HeightOneSpectrum (𝓞 E)),
        (∏ v ∈ s, ((qV E v : ℝ) ^ ∑ i, ν.1 v i)⁻¹) ^ x =
          ∏ v ∈ s, (((qV E v : ℝ) ^ ∑ i, ν.1 v i)⁻¹) ^ x := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha,
          Real.mul_rpow (inv_pos.2 (zpow_pos (hqpos a) _)).le
            (Finset.prod_nonneg fun v _ => (inv_pos.2 (zpow_pos (hqpos v) _)).le), ih]
    rw [hprod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Real.rpow_intCast, ← Real.rpow_neg (hqpos v).le, ← Real.rpow_mul (hqpos v).le]
    push_cast
    ring_nf
  have hD := ((ideleModule E (GeneralLinearGroup.det g)).2 : (0 : ℝ) < _)
  have hQ₀ : 0 ≤ ∏ v ∈ l₀.1.support, ((qV E v : ℝ) ^ ∑ i, l₀.1 v i)⁻¹ :=
    Finset.prod_nonneg fun v _ => (inv_pos.2 (zpow_pos (hqpos v) _)).le
  have hQν0 : 0 ≤ ∏ v ∈ ν.1.support, ((qV E v : ℝ) ^ ∑ i, ν.1 v i)⁻¹ :=
    Finset.prod_nonneg fun v _ => (inv_pos.2 (zpow_pos (hqpos v) _)).le
  rw [hd, hQl, Real.mul_rpow (mul_nonneg hQ₀ hQν0) hD.le, Real.mul_rpow hQ₀ hQν0, hQν, Real.mul_rpow hQ₀ hD.le,
    norm_mul, norm_prod, mul_pow, ← Finset.prod_pow, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

end GlobalTheory.CellPw
end
end
end
