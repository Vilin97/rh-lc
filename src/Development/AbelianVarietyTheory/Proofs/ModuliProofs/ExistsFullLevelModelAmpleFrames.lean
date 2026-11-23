module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmFamilyFiniteUnramifiedOverSiegelFamily
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEquivStdSymp
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFullLevelModelOfFamilyBirationalModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyPelSmoothGenericFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniversalFullLevelOfPelThetaFamilyStatement
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.DenseGenericOfFlat
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCyclotomicBaseRingInvertingPrime
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelFamilyLocalisedCyclotomicIntegersStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptySiegelFamilyOverArithmeticBaseStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyAmpleFramedModelPELThetaFamilyStatement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmFamilyFiniteUnramifiedOverSiegelFamilyStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.cmFamily_finite_unramified_over_siegelFamily : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)), 1 ≤ D.p + D.q → n.Prime → Odd n → (∃ j, 1 ≤ j ∧ N = n ^ j) → FamCore D sM tM lev → (∀ p : ℕ, p.Prime → p ≠ n → ∃ Ag : SiegelFamily (Module.finrank ℚ E / 2 * (D.p + D.q)) p N, SiegRep Ag) → SiegClause D sM tM lev := by
  first | exact @GlobalTheory.siegClause_of_famCore | exact GlobalTheory.siegClause_of_famCore | (intros; apply GlobalTheory.siegClause_of_famCore <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFullLevelModelOfFamilyBirationalModelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_fullLevel_model_of_family_birationalModel : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) (m : ℕ) (C : ZOn sM tM m), 1 ≤ D.p + D.q → AuxiliaryInertOddPrime H n → (∃ j, 1 ≤ j ∧ N = n ^ j) → 0 < m → FamCore D sM tM lev → SiegClause D sM tM lev → ∃ T : Top Xo n N, Nonempty (GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L (m ^ 2)) := by
  first | exact @GlobalTheory.TopOfFamily.exists_top | exact GlobalTheory.TopOfFamily.exists_top | (intros; apply GlobalTheory.TopOfFamily.exists_top <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyPelSmoothGenericFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_thetaFamily_pel_smooth_generic_fibre : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → ArBase em → ∃ (F : ThetaFam n em (PELClass (b := b) D a bas ρ em)) (τ : SAB H F.MM), IsPEL D a bas ρ F.univ τ ∧ SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap o (FractionRing o)))) := by
  first | exact @GlobalTheory.ZM.exists_thetaFam_isPEL_smooth | exact GlobalTheory.ZM.exists_thetaFam_isPEL_smooth | (intros; apply GlobalTheory.ZM.exists_thetaFam_isPEL_smooth <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniversalQuasiProjectiveSiegelFamilyLargeL

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.ZM.SiegelUniversal

theorem isAlgebraic_of_injective {p M : ℕ} (hM : M ≠ 0) {o : Type} [CommRing o] (i : o →+* ZP p M)
    (hi : Function.Injective i) : Algebra.IsAlgebraic ℤ o := by
  have hle : ZP p M ≤ (algebraicClosure ℚ ℂ).toSubalgebra.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro y (rfl | ⟨n, -, rfl⟩)
    · have h1 : zeta M ^ M = 1 := (Complex.isPrimitiveRoot_exp M hM).pow_eq_one
      exact mem_algebraicClosure_iff.2
        (IsAlgebraic.of_pow (Nat.pos_of_ne_zero hM) (h1 ▸ isAlgebraic_one))
    · exact (algebraicClosure ℚ ℂ).inv_mem (natCast_mem _ n)
  refine ⟨fun x => ?_⟩
  rw [← isAlgebraic_algHom_iff ((ZP p M).subtype.comp i).toIntAlgHom (Subtype.val_injective.comp hi),
    IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ, ← mem_algebraicClosure_iff]
  exact hle (i x).2

theorem exists_siegelFamily_siegRep : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ h n : ℕ, 1 ≤ h → n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ p : ℕ, p.Prime → p ≠ n → ∃ Ag : SiegelFamily h p ((n ^ j) ^ 2), SiegRep Ag := by
  intro L L2 hθ hU h n hh hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.nonempty_siegelFamily_over_arithmetic_base L L2 hθ hU h n hh hn hodd
  refine ⟨max j₀ 1, fun j hj p hp hnp => ?_⟩
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  obtain ⟨o, _, b, em, i, hem, hζ, hi, hconst⟩ :=
    GlobalTheory.ZM.CycBase.exists_base n (j * 2) p ((n ^ j) ^ 2) hn hp hnp.symm (by omega) (pow_mul n j 2).symm
  obtain ⟨F⟩ := hj₀ j (le_trans (le_max_left _ _) hj) o b em hem
  have h3 : 3 ≤ n := by
    have := hn.two_le
    rcases hodd with ⟨m, rfl⟩
    omega
  have hk : 3 ≤ (n ^ j) ^ 2 := by
    rw [← pow_mul]
    exact h3.trans (Nat.le_self_pow (by omega) n)
  have hinj : Function.Injective i := fun x y hxy => hem.2.2 (by rw [← hi, ← hi, hxy])
  obtain ⟨Ag, hAg⟩ := GlobalTheory.T.exists_siegelFamily_localised_cyclotomic_integers L L2 h _ p o _ i (hodd.pow.pow) hk hp hinj hζ hconst
    (isAlgebraic_of_injective (by omega) i hinj) F
  obtain ⟨F', -⟩ := F.exists_baseChange i hinj hζ
  obtain ⟨Ag', -, H⟩ := F'.exists_sRep_siegRep (by omega) Ag hAg
  exact ⟨Ag', H⟩

end GlobalTheory.ZM.SiegelUniversal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniversalQuasiProjectiveSiegelFamilyLargeLStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_universal_quasiProjective_siegelFamily_large_level : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ h n : ℕ, 1 ≤ h → n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ p : ℕ, p.Prime → p ≠ n → ∃ Ag : SiegelFamily h p ((n ^ j) ^ 2), SiegRep Ag := by
  first | exact @GlobalTheory.ZM.SiegelUniversal.exists_siegelFamily_siegRep | exact GlobalTheory.ZM.SiegelUniversal.exists_siegelFamily_siegRep | (intros; apply GlobalTheory.ZM.SiegelUniversal.exists_siegelFamily_siegRep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFullLevelModelAmpleFrames

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_ringGenerators (x y : 𝓞 E) : ∃ (J : Type) (_ : Finite J) (a : J → 𝓞 E) (w w' : J),
    a w = x ∧ a w' = y ∧ Subring.closure (Set.range a) = ⊤ := by
  classical
  let b := NumberField.RingOfIntegers.basis E
  refine ⟨Option (Option (Module.Free.ChooseBasisIndex ℤ (𝓞 E))), inferInstance,
    fun j => Option.elim j x (fun j' => Option.elim j' y b), none, some none, rfl, rfl, ?_⟩
  rw [eq_top_iff]
  rintro z -
  have hz : z ∈ Submodule.span ℤ (Set.range b) := by
    rw [b.span_eq]
    exact Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    exact Subring.subset_closure ⟨some (some i), rfl⟩
  | zero => exact zero_mem _
  | add u v _ _ hu hv => exact add_mem hu hv
  | smul m u _ hu => exact zsmul_mem hu m

theorem RZ.coe_rt (H : Host E) (S A : ℕ) : (RZ H S A).subtype (RZ.rt H S A) = H.rt0 := by
  rw [RZ.rt, map_sub, map_mul, map_ofNat, map_one]
  show 2 * ((1 + H.rt0) / 2) - 1 = H.rt0
  ring

theorem exists_tBase_RZ (H : Host E) {n N e : ℕ} (hn : 0 < n) (hN : N = n ^ e) :
    ∃ b : TBase (RZ H n N) N, (b.ζ : RZ H n N) = RZ.ze H n N := by
  have hN0 : N ≠ 0 := by
    rw [hN]
    exact pow_ne_zero _ hn.ne'
  have hζ : IsPrimitiveRoot (zeta N) N := Complex.isPrimitiveRoot_exp N hN0
  have hpow : (RZ.ze H n N) ^ N = 1 := by
    apply Subtype.val_injective
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact hζ.pow_eq_one
  have hinv : ((n : ℂ))⁻¹ ∈ RZ H n N := Subring.subset_closure (Or.inr (Or.inl rfl))
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hunit_n : IsUnit (n : RZ H n N) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, ?_⟩
    apply Subtype.val_injective
    simp [hn']
  have hunit : IsUnit (N : RZ H n N) := by
    have h : (N : RZ H n N) = (n : RZ H n N) ^ e := by rw [← Nat.cast_pow, ← hN]
    rw [h]
    exact hunit_n.pow e
  have key : ∀ {S : Type} [CommRing S] (f : RZ H n N →+* S),
      (Polynomial.cyclotomic N ℤ).eval₂ (Int.castRingHom S) (f (RZ.ze H n N)) =
        f ((Polynomial.cyclotomic N ℤ).eval₂ (Int.castRingHom (RZ H n N)) (RZ.ze H n N)) := by
    intro S _ f
    rw [Polynomial.hom_eval₂]
    congr 1
    exact RingHom.ext_int _ _
  have h0 : (Polynomial.cyclotomic N ℤ).eval₂ (Int.castRingHom (RZ H n N)) (RZ.ze H n N) = 0 := by
    apply Subtype.val_injective
    show (RZ H n N).subtype _ = (RZ H n N).subtype 0
    rw [map_zero, ← key]
    have hr := ((Polynomial.isRoot_cyclotomic_iff_charZero (R := ℂ) (Nat.pos_of_ne_zero hN0)).mpr hζ).eq_zero
    rw [← Polynomial.map_cyclotomic_int, Polynomial.eval_map] at hr
    exact hr
  refine ⟨⟨Units.ofPowEqOne _ N hpow hN0, hunit, ?_⟩, rfl⟩
  intro K _ β
  have : NeZero ((N : ℕ) : K) := ⟨by simpa [map_natCast] using (hunit.map β).ne_zero⟩
  show IsPrimitiveRoot (β (RZ.ze H n N)) N
  apply Polynomial.isRoot_cyclotomic_iff.mp
  show Polynomial.eval _ _ = 0
  rw [← Polynomial.map_cyclotomic_int, Polynomial.eval_map, key, h0, map_zero]

theorem arBase_RZ (H : Host E) {n N e : ℕ} (hn : 0 < n) (hN : N = n ^ e) : ArBase (RZ H n N).subtype := by
  have hN0 : 0 < N := by
    rw [hN]
    exact pow_pos hn e
  have hrt2 : H.rt ^ 2 = -(H.d : 𝓞 E) := H.5
  have hw0 : 2 * H.w0 = 1 + H.rt := H.7
  have hd16 : H.d % 16 = 7 := H.2
  have hconj : ∀ a : 𝓞 E, ((H.bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E) := H.9
  have hd0 : (0 : ℝ) < H.d := by exact_mod_cast H.3.pos

  have hbar_rt : H.bar H.rt = -H.rt := by
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
      have h := congrArg ((↑) : 𝓞 E → E) hrt2
      push_cast at h
      exact h
    have hz2 : (φ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
      rw [← map_pow, hE, map_neg, map_natCast]
    set z := φ (H.rt : E) with hz
    have hx : z.re = 0 := by
      have h1 := congrArg Complex.re hz2
      have h2 := congrArg Complex.im hz2
      simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2
      have h3 : z.re * z.im = 0 := by nlinarith
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exfalso
        rw [h] at h1
        nlinarith [mul_self_nonneg z.re]
    have hc : φ (IsCMField.complexConj E (H.rt : E)) = φ (-(H.rt : E)) := by
      rw [IsCMField.complexEmbedding_complexConj, map_neg, ← hz]
      apply Complex.ext <;> simp [hx]
    have h4 : ((H.bar H.rt : 𝓞 E) : E) = ((-H.rt : 𝓞 E) : E) := by
      rw [hconj, φ.injective hc]
      norm_cast
    exact_mod_cast h4
  obtain ⟨m, hm⟩ : ∃ m, H.d = 16 * m + 7 := ⟨H.d / 16, by omega⟩
  have hdE : (H.d : 𝓞 E) = 16 * m + 7 := by
    rw [hm]
    push_cast
    ring
  have hbal : H.bar (2 + H.rt) = 2 - H.rt := by
    rw [map_add (f := _), map_ofNat, hbar_rt]
    ring
  have hal : (2 + H.rt) ∈ Algebra.adjoin ℤ {H.w0} := by
    have h : 2 + H.rt = 1 + H.w0 + H.w0 := by linear_combination -hw0
    rw [h]
    have hw := Algebra.subset_adjoin (R := ℤ) (Set.mem_singleton H.w0)
    exact add_mem (add_mem (one_mem _) hw) hw

  obtain ⟨l, hl⟩ : ∃ l : Level H, l.A = N := by
    refine ⟨⟨H.d + 4, by omega, ⟨H.d / 2 + 2, by omega⟩, Ideal.span {2 + H.rt}, ?_, ?_, ?_, N, hN0⟩, rfl⟩
    · exact le_antisymm
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
          (Ideal.subset_span ⟨Ideal.subset_span (Set.mem_singleton _), hal⟩)))
        (Ideal.span_le.mpr fun a ha => ha.1)
    · rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_mul_span_singleton]
      congr 2
      rw [RingEquiv.coe_toRingHom, hbal]
      push_cast
      linear_combination -hrt2
    · rw [Ideal.map_span, Set.image_singleton, Ideal.eq_top_iff_one]
      have h1 : (1 : 𝓞 E) = ((4 * m + 3 : 𝓞 E) - (2 - H.rt)) * (2 + H.rt) +
          (4 * m + 3 : 𝓞 E) * H.bar (2 + H.rt) := by
        rw [hbal]
        linear_combination -hrt2 + hdE
      rw [h1]
      exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _)))
  subst hl
  obtain ⟨⟨β, hβ⟩, hft, hded⟩ := BaseRing.isDedFrac_RZ E H l n e hn ⟨1, by rw [hN, Nat.mul_one]⟩
  obtain ⟨⟨_, hD⟩, -, -⟩ := hded β hβ
  exact ⟨hD, hft, Subtype.val_injective⟩

theorem one_le_finrank_div_two : 1 ≤ Module.finrank ℚ E / 2 := by
  have h1 := NumberField.IsTotallyComplex.finrank (K := E)
  have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
  omega

theorem topAmpExists : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → TopAmpExists := by
  intro hHE hL hL2 hSR hTU hUT hZG hRed hGen hTh
  unfold TopAmpExists
  intro E _ _ _ H D hpq Xo n hn
  have hnp : n.Prime := hn.1
  have hno : Odd n := hn.2.1
  have hn0 : 0 < n := hnp.pos
  obtain ⟨bas, hbas⟩ := GlobalTheory.ZM.exists_isSympBasis E H D
  obtain ⟨J, hJ, a, w, w', haw, haw', hcl⟩ := exists_ringGenerators H.w0 (H.bar H.w0)
  have := hJ
  have hg1 : 1 ≤ Module.finrank ℚ E / 2 * (D.p + D.q) :=
    calc 1 = 1 * 1 := rfl
      _ ≤ _ := Nat.mul_le_mul (one_le_finrank_div_two (E := E)) hpq
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.T.exists_thetaFamily_pel_smooth_generic_fibre hL hL2 hRed hGen hTh E H D _ J a w w' bas hpq hbas haw haw' hcl n hnp hno
  obtain ⟨k, j₂, hj₂⟩ := GlobalTheory.T.nonempty_ampleFramedModel_PELThetaFamily hL hL2 hSR hTU hUT hZG E H D n hpq hnp hno
  obtain ⟨j₃, hj₃⟩ := GlobalTheory.T.exists_universal_quasiProjective_siegelFamily_large_level hL hL2 hGen hTh _ n hg1 hnp hno
  obtain ⟨j, hj1, hj2, hj3, hj⟩ : ∃ j, j₁ ≤ j ∧ j₂ ≤ j ∧ j₃ ≤ j ∧ 1 ≤ j :=
    ⟨max (max j₁ j₂) (max j₃ 1), by omega, by omega, by omega, by omega⟩
  have hNe : (n ^ j) ^ 2 = n ^ (j * 2) := (pow_mul n j 2).symm
  obtain ⟨b, hb⟩ := exists_tBase_RZ H hn0 hNe
  have hAr := arBase_RZ H hn0 hNe
  obtain ⟨F, τ, hPEL, hsm⟩ := hj₁ j hj1 (RZ H n ((n ^ j) ^ 2)) b (RZ H n ((n ^ j) ^ 2)).subtype
    (RZ.rt H n ((n ^ j) ^ 2)) (RZ.coe_rt H n _) hAr
  obtain ⟨C⟩ := hj₂ j hj2 (n ^ j) rfl _ J a bas b F τ hbas hcl ⟨w, w', haw, haw'⟩ hb hPEL hsm
  obtain ⟨lev, hcore⟩ := GlobalTheory.T.exists_universal_fullLevel_of_pelThetaFamily hL hL2 E H D n (n ^ j) _ J a bas b F τ hbas hcl
    ⟨w, w', haw, haw'⟩ hb hPEL hsm hpq hnp hno ⟨j, hj, rfl⟩
  have hcl2 := GlobalTheory.T.cmFamily_finite_unramified_over_siegelFamily hHE hL hL2 E H D n ((n ^ j) ^ 2) F.MM F.s τ lev hpq hnp hno
    ⟨j * 2, by omega, hNe⟩ hcore (hj₃ j hj3)
  obtain ⟨T, hT⟩ := GlobalTheory.T.exists_fullLevel_model_of_family_birationalModel hHE hL hL2 E H D Xo n ((n ^ j) ^ 2) F.MM F.s τ lev (n ^ k) C hpq hn
    ⟨j * 2, by omega, hNe⟩ (pow_pos hn0 k) hcore hcl2
  refine ⟨j * 2, k, ?_⟩
  rw [← hNe]
  exact ⟨T, by omega, hT⟩

end GlobalTheory.Models
end
end
