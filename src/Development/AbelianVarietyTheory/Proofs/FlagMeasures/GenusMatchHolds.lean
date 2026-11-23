module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicColumnLatticeEqSpanPartTransportedFrameStatement
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeCarryIffForallPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryOfFiniteSupportStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLocalUnitaryLatticesOfLevelStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLocalUnitaryOfSelfDualAtPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocallySelfDualOfHermitianLatticeOfLevelStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVSDBwdHolds
public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepLevelTLat
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedColumnLatticeHasLevelAndDualGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryDatumLevelPrimeSplitDegreeGramFacts
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntSmulIsIntegral

section

@[expose] public section

namespace GlobalTheory.IntSmulIsIntegral

theorem exists_int_smul_isIntegral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ (d • a) := by
  have h : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  exact h.exists_integral_multiple

theorem exists_int_smul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (M : Submodule (NumberField.RingOfIntegers E) (Fin n → E))
    (hM : Submodule.span E (↑M : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ (c : ℤ), c ≠ (0 : ℤ) ∧ c • x ∈ M := by
  apply Formalism.L2.SG.Pf.NcVal.OmVSt.OmX.exists_int_smul_mem <;> assumption

end GlobalTheory.IntSmulIsIntegral
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalSpanOfLatticeAtPlaceEqForAlmostAllPlaces

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

section Global

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_zsmul_mem_of_span (M : Submodule (𝓞 E) (Fin n → E))
    (hM : Submodule.span E (M : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ c : ℤ, c ≠ 0 ∧ c • x ∈ M := by
  first
  | exact @_root_.GlobalTheory.IntSmulIsIntegral.exists_int_smul_mem
  | exact _root_.GlobalTheory.IntSmulIsIntegral.exists_int_smul_mem
  | (apply _root_.GlobalTheory.IntSmulIsIntegral.exists_int_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntSmulIsIntegral.exists_int_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntSmulIsIntegral.exists_int_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntSmulIsIntegral.exists_int_smul_mem ..)

theorem exists_zsmul_le (L M : Submodule (𝓞 E) (Fin n → E)) (hL : Module.Finite (𝓞 E) L)
    (hM : Submodule.span E (M : Set (Fin n → E)) = ⊤) :
    ∃ c : ℤ, c ≠ 0 ∧ ∀ x ∈ L, c • x ∈ M := by
  obtain ⟨S, hS⟩ : L.FG := Module.Finite.iff_fg.mp hL
  have hfin : ∀ T : Finset (Fin n → E), ∃ c : ℤ, c ≠ 0 ∧ ∀ x ∈ T, c • x ∈ M := by
    classical
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | insert a T _ ih =>
      obtain ⟨c, hc, hcT⟩ := ih
      obtain ⟨d, hd, hda⟩ := exists_zsmul_mem_of_span M hM a
      refine ⟨d * c, mul_ne_zero hd hc, fun x hx => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rw [mul_comm, mul_smul]
        exact zsmul_mem hda c
      · rw [mul_smul]
        exact zsmul_mem (hcT x hx) d
  obtain ⟨c, hc, hcS⟩ := hfin S
  refine ⟨c, hc, fun x hx => ?_⟩
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hcS x hx
  | zero => simp
  | add a b _ _ ha hb =>
    rw [smul_add]
    exact M.add_mem ha hb
  | smul a y _ hy =>
    rw [smul_comm]
    exact M.smul_mem a hy

end Global

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem int_inv_mem_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) (c : ℤ)
    (hv : (c : 𝓞 F) ∉ v.asIdeal) :
    (algebraMap F (v.adicCompletion F) (c : F))⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : Valued.v (algebraMap F (v.adicCompletion F) (c : F)) = 1 := by
    have h2 : (c : F) = algebraMap (𝓞 F) F (c : 𝓞 F) := by simp
    have h3 : Valued.v (algebraMap F (v.adicCompletion F) (c : F)) = v.valuation F (c : F) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (c : F)
    rw [h3, h2, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.mpr hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1, inv_one]

theorem loc_le_of_zsmul (v : HeightOneSpectrum (𝓞 F)) (L M : Submodule (𝓞 E) (Fin n → E)) (c : ℤ)
    (hc : c ≠ 0) (hv : (c : 𝓞 F) ∉ v.asIdeal) (h : ∀ x ∈ L, c • x ∈ M) : loc v L ≤ loc v M := by
  have hu := int_inv_mem_adicCompletionIntegers v c hv
  set u : v.adicCompletion F := (algebraMap F (v.adicCompletion F) (c : F))⁻¹ with hudef
  have hne : algebraMap F (v.adicCompletion F) (c : F) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact_mod_cast hc
  have hs : (1 : E) ⊗ₜ[F] u ∈ intV E v :=
    Subring.subset_closure (Or.inr ⟨⟨u, hu⟩, rfl⟩)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨x, hx, rfl⟩
  have hgen : (fun i => inclE (F := F) (v.adicCompletion F) ((c • x) i)) ∈ loc (F := F) v M :=
    Submodule.subset_span ⟨c • x, h x hx, rfl⟩
  have hm := (loc (F := F) v M).smul_mem ⟨_, hs⟩ hgen
  suffices heq : (fun i => inclE (F := F) (v.adicCompletion F) (x i)) =
      (⟨(1 : E) ⊗ₜ[F] u, hs⟩ : intV E v) • (fun i => inclE (F := F) (v.adicCompletion F) ((c • x) i)) by
    show (fun i => inclE (F := F) (v.adicCompletion F) (x i)) ∈ loc (F := F) v M
    rw [heq]
    exact hm
  funext i
  have hci : (c • x) i = (c : F) • x i := by
    simp [Int.cast_smul_eq_zsmul]
  have hone : (c : F) • u = 1 := by
    rw [Algebra.smul_def, hudef, mul_inv_cancel₀ hne]
  show (x i) ⊗ₜ[F] (1 : v.adicCompletion F) = ((1 : E) ⊗ₜ[F] u) * ((c • x) i ⊗ₜ[F] (1 : v.adicCompletion F))
  rw [Algebra.TensorProduct.tmul_mul_tmul, hci, one_mul, mul_one, TensorProduct.smul_tmul, hone]

end Local

theorem loc_eq_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), IsLat L → IsLat M →
    {v : HeightOneSpectrum (𝓞 F) | loc v L ≠ loc v M}.Finite := by
  intro F E _ _ _ _ _ n L M hL hM
  obtain ⟨c, hc, hcLM⟩ := exists_zsmul_le L M hL.1 hM.2
  obtain ⟨d, hd, hdML⟩ := exists_zsmul_le M L hM.1 hL.2
  have hcd : (((c * d : ℤ) : 𝓞 F)) ≠ 0 := by
    exact_mod_cast mul_ne_zero hc hd
  have hI : Ideal.span {(((c * d : ℤ) : 𝓞 F))} ≠ 0 := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hcd
  refine (Ideal.finite_factors hI).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_span_singleton]
  by_contra hn
  have hcv : (c : 𝓞 F) ∉ v.asIdeal := fun h => hn (by
    rw [Int.cast_mul]
    exact Ideal.mul_mem_right _ _ h)
  have hdv : (d : 𝓞 F) ∉ v.asIdeal := fun h => hn (by
    rw [Int.cast_mul]
    exact Ideal.mul_mem_left _ _ h)
  exact hv (le_antisymm (loc_le_of_zsmul v L M c hc hcv hcLM) (loc_le_of_zsmul v M L d hd hdv hdML))

end GlobalTheory.St.G

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalSpanOfLatticeAtPlaceEqForAlmostAllPlacesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.localSpanOfLatticeAtPlace_eq_for_almost_all_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), IsLat L → IsLat M → {v : HeightOneSpectrum (𝓞 F) | loc v L ≠ loc v M}.Finite := by
  first | exact @GlobalTheory.St.G.loc_eq_almost_all | exact GlobalTheory.St.G.loc_eq_almost_all | (intros; apply GlobalTheory.St.G.loc_eq_almost_all <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticesLevelOneGenus

section

@[expose] public section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem tlat_one_genus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → TLat cm.sig J T f M → ∃ h : UPts cm.sig J (Ad F), ∀ x, (h⁻¹).1.1 *ᵥ x ∈ hat F L ↔ x ∈ hat F M := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f L M hT hS hf hL hM
  classical
  have hLat : IsLat L := hL.1
  have hMat : IsLat M := hM.1

  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ g ∈ UPts cm.sig J (v.adicCompletion F),
      ∀ x, x ∈ loc v L ↔ g.1 *ᵥ x ∈ loc v M := by
    intro v
    by_cases hv : (T : 𝓞 F) ∈ v.asIdeal
    · exact GlobalTheory.T.exists_localUnitary_lattices_of_level F E cm n J hJ hdet T f L M hT hS hf hL hM v hv
    · exact GlobalTheory.T.exists_localUnitary_of_selfDual_at_place F E cm n J hJ hdet L M hLat hMat v
        (GlobalTheory.T.isLocallySelfDual_of_hermitianLatticeOfLevel F E cm n J hJ hdet T f L hL v hv)
        (GlobalTheory.T.isLocallySelfDual_of_hermitianLatticeOfLevel F E cm n J hJ hdet T f M hM v hv)
  choose g hgU hg using hloc

  let k : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (E ⊗[F] v.adicCompletion F) :=
    fun v => if loc v L = loc v M then 1 else g v
  have hkU : ∀ v, k v ∈ UPts cm.sig J (v.adicCompletion F) := by
    intro v
    by_cases hv : loc v L = loc v M
    · simp only [k, if_pos hv]; exact one_mem _
    · simp only [k, if_neg hv]; exact hgU v
  have hfin : {v | k v ≠ 1}.Finite := by
    refine (GlobalTheory.T.localSpanOfLatticeAtPlace_eq_for_almost_all_places F E n L M hLat hMat).subset ?_
    intro v hv heq
    exact hv (by simp only [k, if_pos heq])
  obtain ⟨y, hyU, hy⟩ := GlobalTheory.T.exists_adelic_unitary_of_finite_support F E n cm.sig J k hkU hfin
  have hglob : ∀ x, x ∈ hat F L ↔ y.1 *ᵥ x ∈ hat F M := by
    rw [GlobalTheory.T.adelicLattice_carry_iff_forall_place F E n L M hLat hMat y]
    intro v x
    rw [hy v]
    by_cases hv : loc v L = loc v M
    · simp only [k, if_pos hv, Units.val_one, Matrix.one_mulVec, hv]
    · simp only [k, if_neg hv]; exact hg v x
  refine ⟨⟨y, hyU⟩, fun x => ?_⟩
  rw [hglob, Matrix.mulVec_mulVec]
  have hinv : ((⟨y, hyU⟩ : UPts cm.sig J (Ad F))⁻¹).1 = y⁻¹ := rfl
  rw [hinv, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

end GlobalTheory.St.G
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticesLevelOneGenusStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.hermitianLattices_level_one_genus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → TLat cm.sig J T f M → ∃ h : UPts cm.sig J (Ad F), ∀ x, (h⁻¹).1.1 *ᵥ x ∈ hat F L ↔ x ∈ hat F M := by
  first | exact @GlobalTheory.St.G.tlat_one_genus | exact GlobalTheory.St.G.tlat_one_genus | (intros; apply GlobalTheory.St.G.tlat_one_genus <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusMatchHolds

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G

theorem genusMatch_holds : ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), GenusMatch D F := by
  intro D F X u wt ιA hW hA
  obtain ⟨hT, -, -, hdeg, -, hH, hdet⟩ := record_facts D u
  have hM := (GlobalTheory.T.transported_column_lattice_has_level_and_dual_generator D X u wt hW).1
  have hL := stepLevel_tLat (S := (F u).cls0.lev)
  have hE := (GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hA).1
  obtain ⟨h, hh⟩ := GlobalTheory.T.hermitianLattices_level_one_genus D.host.F D.host.E D.sp.cm (D.R.N 0) _ hH hdet (D.mem u).A.T D.R.f
    (F u).cls0.lev.Lb (Mq wt) (D.mem u).A.T_prime hT hdeg hL hM
  exact ⟨h, fun x => (hh x).trans (hE x)⟩

end GlobalTheory.St.G
end
end
