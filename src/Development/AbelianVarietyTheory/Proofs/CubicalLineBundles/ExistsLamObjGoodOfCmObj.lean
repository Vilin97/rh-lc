module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.BarEqOfLamEqMultiplier
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmHostRootNegDiscriminantNeNegSelf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRingStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCommonDenominatorOfValuationLeOne
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenySumOfCmHoms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieEigenbasisGenericFibreCmTripleStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsDvrModelLieBasisAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsFibreOfIffIsPolFibre
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsModelAtIntegralIffMemLieLat
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegersStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LinearIndependentOfIsLieBasis
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ValuationLeIffExistsSmulMem
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.NormNum.Parity
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRosatiActionWeilPairingBalancedTriple
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignatureStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MapRtEqNegIff
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CommutatorPairingsEqOfCubeLBPairingIso
import Mathlib.AlgebraicGeometry.Modules.Sheaf

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenySumOfCmHomsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF


theorem _root_.GlobalTheory.T.exists_inverse_isogeny_sum_of_cm_homs : ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A A' B : Out.PolAV (Sp (𝓞 K))) (p q : ℕ) (φ : Fin p → (A.A ⟶ B.A)) (φ' : Fin q → (A'.A ⟶ B.A)), (∀ i, IsMonHom (φ i)) → (∀ i, IsMonHom (φ' i)) → B.g = p * A.g + q * A'.g → (∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ B.A, ∃ (x : Fin p → (Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.A)) (x' : Fin q → (Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A'.A)), y = (List.ofFn fun i => x i ≫ φ i).prod * (List.ofFn fun i => x' i ≫ φ' i).prod) → ∃ (N : ℕ) (ψ : Fin p → (B.A ⟶ A.A)) (ψ' : Fin q → (B.A ⟶ A'.A)), 0 < N ∧ (∀ (Tb : Over (Sp (𝓞 K))) (x : Tb ⟶ B.A), padd B.A (psumPt fun i => x ≫ ψ i ≫ φ i) (psumPt fun i => x ≫ ψ' i ≫ φ' i) = pnsmulPt N x) ∧ ∀ (Tb : Over (Sp (𝓞 K))) (a : Fin p → (Tb ⟶ A.A)) (a' : Fin q → (Tb ⟶ A'.A)), (∀ i, padd B.A (psumPt fun k => a k ≫ φ k) (psumPt fun k => a' k ≫ φ' k) ≫ ψ i = pnsmulPt N (a i)) ∧ ∀ i, padd B.A (psumPt fun k => a k ≫ φ k) (psumPt fun k => a' k ≫ φ' k) ≫ ψ' i = pnsmulPt N (a' i) := by
  first | exact @GlobalTheory.LamF.exists_inverse_isogeny_of_sum | exact GlobalTheory.LamF.exists_inverse_isogeny_of_sum | (intros; apply GlobalTheory.LamF.exists_inverse_isogeny_of_sum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMetrisedLineOfLieVector

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_fractionalIdeal_single_mem {K : Type} [Field K] [NumberField K] {n : ℕ} (Λ : Submodule (𝓞 K) (Fin n → K))
    (hfg : Λ.FG) (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) (i : Fin n) :
    ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K, I ≠ 0 ∧ ∀ c : K, c ∈ I ↔ Pi.single i c ∈ Λ := by
  let J : Submodule (𝓞 K) K := Λ.comap (LinearMap.single (𝓞 K) (fun _ : Fin n => K) i)
  have hle : J ≤ Λ.map (LinearMap.proj i) := fun c hc => ⟨_, hc, by simp⟩
  have hJ : J.FG := by
    haveI := isNoetherian_of_fg_of_noetherian _ (hfg.map (LinearMap.proj (R := 𝓞 K) (φ := fun _ : Fin n => K) i))
    exact isNoetherian_submodule.1 this _ hle
  refine ⟨⟨J, FractionalIdeal.isFractional_of_fg hJ⟩, fun h0 => ?_, fun c => Iff.rfl⟩
  have h1 : (Pi.single i 1 : Fin n → K) ∈ Submodule.span K (Λ : Set (Fin n → K)) := hsp ▸ trivial
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ _ h1
  rw [Submodule.span_eq] at ht
  have h2 : algebraMap (𝓞 K) K t ∈ J := by
    change Pi.single i _ ∈ Λ
    rw [Algebra.algebraMap_eq_smul_one, Pi.single_smul]
    exact ht
  have h3 : J = ⊥ := (congrArg FractionalIdeal.coeToSubmodule h0).trans FractionalIdeal.coe_zero
  rw [h3, Submodule.mem_bot] at h2
  exact nonZeroDivisors.coe_ne_zero t (FaithfulSMul.algebraMap_injective _ K (h2.trans (map_zero _).symm))

theorem exists_length_of_lieVec (hU : ThetaUnifAV) {K : Type} [Field K] (x : KeyIn K) (i : Fin x.P.g) (σ : K →+* ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∃ (xσ : KeyIn ℂ) (u : HolUnif xσ.P.A xσ.P.L xσ.P.g) (Hm : Matrix (Fin xσ.P.g) (Fin xσ.P.g) ℂ)
      (χ : u.Λ → ℂ) (W : Fin xσ.P.g → ℂ) (hg : xσ.P.g = x.P.g),
      KeyPB xσ x σ ∧ u.IsAH Hm χ ∧ u.IsDiff W (xσ.v (i.cast hg.symm)) ∧
      r ^ 2 = Real.pi * (W ⬝ᵥ Hm.mulVec (star W)).re := by
  obtain ⟨xσ, hx⟩ := KeyPow.exists_keyPB x σ
  have hg : xσ.P.g = x.P.g := by
    obtain ⟨_, _, _, hg, _⟩ := hx
    exact hg
  obtain ⟨u, Hm, χ, -, hA, -, hd, hd', -⟩ := hU xσ.P xσ.rig xσ.rig_gen
  choose W hW using fun i => (hd _ (xσ.basis.1 i)).exists
  have hne := (LieMetric.linearIndependent_of_isLieBasis u hd' xσ.basis hW).ne_zero (i.cast hg.symm)
  have hpos := mul_pos Real.pi_pos (hA.2.1 _ hne)
  exact ⟨_, Real.sqrt_pos.2 hpos, xσ, u, Hm, χ, _, hg, hx, hA, hW _, Real.sq_sqrt hpos.le⟩

theorem exists_isVecLine : Out.SecTwistSt → ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left), IsFibreOf A x (gmap K) φ → ∀ i : Fin x.P.g, ∃ ℓ : MLine K, IsVecLine A x φ i ℓ := by
  intro hT hU _ K _ _ A x φ hφ i
  have hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ := (isFibreOf_iff_isPolFibre _ _ _ A x φ).1 hφ
  obtain ⟨hfg, hsp⟩ := GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers K A (GenFib.mk x.P φ hf x.v x.basis)
  obtain ⟨I, hI, hmem⟩ := exists_fractionalIdeal_single_mem _ hfg hsp i
  choose r hr H using exists_length_of_lieVec hU x i
  refine ⟨⟨I, r⟩, ⟨hI, hr⟩, fun p => ?_, H⟩
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_dvrModel_lieBasis_at_prime hT K A x φ hφ p
  obtain ⟨⟨cl, -, hcl⟩, hiff⟩ := (local_global_ideal_lattice K).2.1 I p hI
  refine ⟨M, cl, hM, hcl, fun c => ?_⟩
  rw [((hiff cl).1 hcl).2 c, ← Matrix.smul_vecMul, isModelAt_integral_iff_mem_lieLat K A x φ hf p M hM]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  rw [hmem, Pi.single_smul, ← Pi.single_smul, smul_eq_mul, _root_.mul_one]

end GlobalTheory.LamF
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMetrisedLineOfLieVectorStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF


theorem _root_.GlobalTheory.T.exists_metrised_line_of_lieVector : Out.SecTwistSt → ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left), IsFibreOf A x (gmap K) φ → ∀ i : Fin x.P.g, ∃ ℓ : MLine K, IsVecLine A x φ i ℓ := by
  first | exact @GlobalTheory.LamF.exists_isVecLine | exact GlobalTheory.LamF.exists_isVecLine | (intros; apply GlobalTheory.LamF.exists_isVecLine <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRosatiActionWeilPairingBalancedTripleStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF


theorem _root_.GlobalTheory.T.exists_rosatiAction_weilPairing_balanced_triple : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E), (∀ a : 𝓞 E, star a = H.bar a) → ∀ (K : Type) [Field K] [NumberField K] (T : PAT H (Sp (𝓞 K))), ∃ oa : T.pol.OAct (𝓞 E), oa.act = T.t.act.act ∧ RosatiConj T.pol oa := by
  first | exact @GlobalTheory.LamF.exists_oAct_rosatiConj | exact GlobalTheory.LamF.exists_oAct_rosatiConj | (intros; apply GlobalTheory.LamF.exists_oAct_rosatiConj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilPairingIffOfCubeLBPairingIso

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem weilIs_iff_of_lamEq_id : Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (A B : Out.PolAV (Sp (𝓞 K))) (f : A.A ⟶ B.A) (g : A.A ⟶ A.A), IsMonHom f → IsMonHom g → LamEq B.L f f A.L g (𝟙 A.A) → ∀ (Tb : Over (Sp (𝓞 K))) (k : ℕ) (x y : Tb ⟶ A.A) (c : Γ(Tb.left, ⊤)ˣ), 0 < k → pnsmulPt k x = toUnit Tb ≫ η[A.A] → pnsmulPt k y = toUnit Tb ≫ η[A.A] → (Out.WeilIs B.A B.L k (x ≫ f) (y ≫ f) c ↔ Out.WeilIs A.A A.L k (x ≫ g) y c) := by
  intro hL K _ _ A B f g hf hg hlam Tb k x y c hk hx hy
  have h1 : toUnit Tb ≫ η[A.A] = (1 : Tb ⟶ A.A) := rfl
  have hp (n : ℕ) (a : Tb ⟶ A.A) : pnsmulPt n a = a ^ n := by
    induction n with
    | zero => rw [pow_zero]; rfl
    | succ n ih => rw [pow_succ, ← ih]; rfl
  rw [hp, h1] at hx hy
  have h := PairingScheme.weilIs_iff_of_lamEq hL (𝓞 K) A A B A f f g (𝟙 A.A) hf hf hg inferInstance hlam
    Tb k x y c hk hx hy
  rwa [Category.comp_id] at h

end GlobalTheory.LamF
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilPairingIffOfCubeLBPairingIsoStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF


theorem _root_.GlobalTheory.T.weilPairing_iff_of_cubeLBPairingIso : Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (A B : Out.PolAV (Sp (𝓞 K))) (f : A.A ⟶ B.A) (g : A.A ⟶ A.A), IsMonHom f → IsMonHom g → LamEq B.L f f A.L g (𝟙 A.A) → ∀ (Tb : Over (Sp (𝓞 K))) (k : ℕ) (x y : Tb ⟶ A.A) (c : Γ(Tb.left, ⊤)ˣ), 0 < k → pnsmulPt k x = toUnit Tb ≫ η[A.A] → pnsmulPt k y = toUnit Tb ≫ η[A.A] → (Out.WeilIs B.A B.L k (x ≫ f) (y ≫ f) c ↔ Out.WeilIs A.A A.L k (x ≫ g) y c) := by
  first | exact @GlobalTheory.LamF.weilIs_iff_of_lamEq_id | exact GlobalTheory.LamF.weilIs_iff_of_lamEq_id | (intros; apply GlobalTheory.LamF.weilIs_iff_of_lamEq_id <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLamObjGoodOfCmObj

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section
namespace GlobalTheory.LamF

theorem prod_ofFn_sum {M : Type} [Monoid M] {p q : ℕ} (f : Fin p ⊕ Fin q → M) :
    (List.ofFn fun i : Fin (p + q) => f (finSumFinEquiv.symm i)).prod =
      (List.ofFn fun i => f (Sum.inl i)).prod * (List.ofFn fun i => f (Sum.inr i)).prod := by
  rw [List.ofFn_add, List.prod_append]
  congr 2
  · congr 1
    funext i
    exact congrArg f (finSumFinEquiv_symm_apply_castAdd i)
  · congr 1
    funext i
    exact congrArg f (finSumFinEquiv_symm_apply_natAdd i)

theorem lamEq_adj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S)
    (a : 𝓞 E) : LamEq t.PP.L (t.act.act a) (𝟙 t.G) t.PP.L (𝟙 t.G) (t.act.act (H.bar a)) := by
  have := t.adj a
  unfold LamEq
  rw [Category.comp_id, Category.comp_id]
  exact this

theorem exists_lamObjGood_of_cmObj : Out.SecTwistSt → ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l), (∀ a : 𝓞 E, star a = H.bar a) → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q) (La : ℝ), (∀ τ, τ ∈ psiSet H ↔ labK c K τ (H.rt : E) = (ρ : K)) → (∀ j (τ : E →+* ℂ), ‖τ (X.hh j : E)‖ ≤ La ^ 2) → ∀ (xB : KeyIn K) (φB : xB.P.A.left ⟶ X.B.pol.A.left), IsFibreOf X.B.pol xB (gmap K) φB → ∃ (oa : X.B.pol.OAct (𝓞 E)) (oaΨ : (X.A true).pol.OAct (𝓞 E)) (oa' : (X.A false).pol.OAct (𝓞 E)) (xΨ x' : KeyIn K) (φΨ : xΨ.P.A.left ⟶ (X.A true).pol.A.left) (φ' : x'.P.A.left ⟶ (X.A false).pol.A.left) (τΨ : Fin xΨ.P.g ≃ {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}) (τ' : Fin x'.P.g ≃ {τ : E →+* ℂ // τ (H.rt : E) ≠ H.rt0}) (ℓΨ : Fin xΨ.P.g → MLine K) (ℓ' : Fin x'.P.g → MLine K) (Tl LamL : MLine K), oa.act = X.B.t.act.act ∧ oaΨ.act = (X.A true).t.act.act ∧ oa'.act = (X.A false).t.act.act ∧ LamObjGood (LamObj.mk (c := c) (nΨ := p) (n' := q) K X.B.pol oa (X.A true).pol oaΨ (X.A false).pol oa' (fun i => X.φ (Sum.inl i)) (fun i => X.φ (Sum.inr i)) (fun i => X.hh (Sum.inl i)) (fun i => X.hh (Sum.inr i)) xB xΨ x' φB φΨ φ' τΨ τ' ℓΨ ℓ' Tl LamL) (Module.finrank ℚ E / 2) La := by
  intro hS hU hL hX E _ _ _ _ H l c hstar K _ _ _ ρ σ₁ p q X La hρ hLa xB φB hB
  obtain ⟨hbij, -, -, ρ', -, h₁, h₂, hc, -⟩ := labK_spec E H l c K
  have hfpos : 0 < Module.finrank ℚ E / 2 := by
    have e := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at e
    have : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
    omega
  have hρρ : ρ' = ρ := by
    have : Nonempty (psiSet H) := (Nat.card_pos_iff.1 (hc ▸ hfpos)).1
    obtain ⟨τ, hτ⟩ := this
    exact Subtype.ext (((h₁ τ).1 hτ).symm.trans ((hρ τ).1 hτ))
  subst hρρ
  obtain ⟨oa, hoa, hR⟩ := GlobalTheory.T.exists_rosatiAction_weilPairing_balanced_triple hL E H hstar K X.B
  obtain ⟨oaΨ, hoaΨ, hRΨ⟩ := GlobalTheory.T.exists_rosatiAction_weilPairing_balanced_triple hL E H hstar K (X.A true)
  obtain ⟨oa', hoa', hR'⟩ := GlobalTheory.T.exists_rosatiAction_weilPairing_balanced_triple hL E H hstar K (X.A false)
  obtain ⟨xΨ, φΨ, τΨ, hFΨ, hgΨ, hTΨ⟩ := GlobalTheory.T.exists_lie_eigenbasis_genericFibre_cmTriple hS hL E H K (X.A true) oaΨ (psiSet H) (labK c K) ρ' hoaΨ hbij
    X.ρ_sq hρ X.typeP
  obtain ⟨x', φ', τ', hF', hg', hT'⟩ := GlobalTheory.T.exists_lie_eigenbasis_genericFibre_cmTriple hS hL E H K (X.A false) oa' (psiSet H)ᶜ (labK c K) (-ρ') hoa' hbij
    (by rw [neg_sq, X.ρ_sq]) h₂ ((hasType_neg_iff E H _ _ _ ρ' 0 1 X.ρ_sq).1 X.typeM)
  choose ℓΨ hℓΨ using GlobalTheory.T.exists_metrised_line_of_lieVector hS hU hL K _ xΨ φΨ hFΨ
  choose ℓ' hℓ' using GlobalTheory.T.exists_metrised_line_of_lieVector hS hU hL K _ x' φ' hF'
  obtain ⟨Tl, LamL, k₁, k₂, k₃, k₄, k₅⟩ := GlobalTheory.LamF.exists_keyLines hS hU hL hX K _ xB φB hB
  have pB := (isFibreOf_iff_isPolFibre _ _ (algebraMap (𝓞 K) K) _ xB φB).1 hB
  have pΨ := (isFibreOf_iff_isPolFibre _ _ (algebraMap (𝓞 K) K) _ xΨ φΨ).1 hFΨ
  have p' := (isFibreOf_iff_isPolFibre _ _ (algebraMap (𝓞 K) K) _ x' φ').1 hF'
  have gB : X.B.g = Module.finrank ℚ E / 2 * (p + q) :=
    (GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ' X.B ⟨xB.P, φB, pB, xB.v, xB.basis⟩ p q X.split X.typeB X.ρ_sq).2.2.2.1
  have gA : ∀ b, (X.A b).g = Module.finrank ℚ E / 2 := fun b => by
    cases b
    · exact p'.1.symm.trans hg'
    · exact pΨ.1.symm.trans hgΨ
  have hlam : ∀ j, LamEq X.B.pol.L (X.φ j) (X.φ j) (X.A j.isLeft).pol.L ((X.A j.isLeft).t.act.act (X.hh j))
      (𝟙 (X.A j.isLeft).pol.A) := fun j =>
    (GlobalTheory.T.cubeLBPairingIso_iff_weilPairingCompatible_over_ring hL (𝓞 K) (X.A j.isLeft).pol (X.A j.isLeft).pol X.B.pol (X.A j.isLeft).pol _ _ _ _
      (X.lin j).isMonHom (X.lin j).isMonHom ((X.A j.isLeft).t.act.hom _) inferInstance ℂ
      (σ₁.comp (algebraMap (𝓞 K) K))).2 inferInstance
      (σ₁.injective.comp (IsFractionRing.injective (𝓞 K) K)) (X.weil j)
  have hsym : ∀ j, star (X.hh j) = X.hh j := fun j => (hstar _).trans
    (GlobalTheory.LamF.bar_eq_of_lamEq_multiplier hL E H K (X.A j.isLeft).pol X.B.pol (X.A j.isLeft).t.act (X.φ j) (X.hh j)
      (by change 1 ≤ (X.A j.isLeft).g; rw [gA]; exact hfpos) (lamEq_adj _) (hlam j))
  have hpol := fun j : Fin p ⊕ Fin q => GlobalTheory.T.weilPairing_iff_of_cubeLBPairingIso hL K (X.A j.isLeft).pol X.B.pol (X.φ j) ((X.A j.isLeft).t.act.act (X.hh j))
    (X.lin j).isMonHom ((X.A j.isLeft).t.act.hom (X.hh j)) (hlam j)
  refine ⟨oa, oaΨ, oa', xΨ, x', φΨ, φ', τΨ, τ', ℓΨ, ℓ', Tl, LamL, hoa, hoaΨ, hoa', ?_⟩
  refine ⟨hR, hRΨ, hR', hB, hFΨ, hF', hgΨ, hg', pB.1.trans gB, hTΨ, hT', fun i a => ?_, fun i a => ?_,
    ⟨fun i => (X.lin (Sum.inl i)).isMonHom, fun i => (X.lin (Sum.inr i)).isMonHom, ?_⟩,
    ⟨fun i => hsym (Sum.inl i), fun i => hsym (Sum.inr i), fun i => ?_, fun i => ?_⟩,
    ⟨fun i => hLa (Sum.inl i), fun i => hLa (Sum.inr i)⟩, hℓΨ, hℓ', k₁, k₂, k₃, k₄, k₅⟩
  · dsimp only
    rw [hoa, hoaΨ]
    exact (X.lin (Sum.inl i)).comm a
  · dsimp only
    rw [hoa, hoa']
    exact (X.lin (Sum.inr i)).comm a
  · refine GlobalTheory.T.exists_inverse_isogeny_sum_of_cm_homs hU hL hX K σ₁ (X.A true).pol (X.A false).pol X.B.pol p q _ _
      (fun i => (X.lin (Sum.inl i)).isMonHom) (fun i => (X.lin (Sum.inr i)).isMonHom) ?_ fun y => ?_
    · change X.B.g = p * (X.A true).g + q * (X.A false).g
      rw [gB, gA, gA]
      ring
    · obtain ⟨x, hx⟩ := X.onto y
      exact ⟨fun i => x (Sum.inl i), fun i => x (Sum.inr i), hx.trans (prod_ofFn_sum fun j => x j ≫ X.φ j)⟩
  · dsimp only
    rw [hoaΨ]
    exact hpol (Sum.inl i)
  · dsimp only
    rw [hoa']
    exact hpol (Sum.inr i)

end GlobalTheory.LamF
end
end
end
