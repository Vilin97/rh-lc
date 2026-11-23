module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfValHomEq
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsHomogenisation
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat
public import Mathlib.RingTheory.Nullstellensatz
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
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
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.VanishingIdealConePrimeHomogeneous
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.CardZerosOnTorsionCosetLe
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsBasisOfIsField
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsSectionRing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.NonemptyGradedAlgebraSubGrading
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsIsoOfEqualCoordinateConesStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelThetaPtOfPolarisedIsoStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.HomogeneousCoordsOfIsValueAtFrameStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsClosedImmersionOfSpanLinePowerSectionsStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.LbIsoPullOfHomPreservingCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.LevelBasisEqOfSameThetaPtStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.MemVanishingIdealOfFormVanishingTorsion
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaFamilyOriginGermOfMultiplicationStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaPtSupportMeetsEveryCosetStatement
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HilbEqFinrankQuotPiece

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem hilb_eq_finrank_quotPiece {k J : Type} [Field k] [Finite J] (C : Set (J → k)) (d : ℕ) :
    hilb C d = Module.finrank k (quotPiece (MvPolynomial.vanishingIdeal k C) (d : ℤ)) := by
  rw [quotPiece_natCast]
  let ev : MvPolynomial J k →ₐ[k] (C → k) :=
    AlgHom.pi fun v : C => MvPolynomial.aeval v.1
  have hker : ∀ a ∈ MvPolynomial.vanishingIdeal k C, ev a = 0 := fun a ha =>
    funext fun v => ha v.1 v.2
  let φ := Ideal.Quotient.liftₐ (MvPolynomial.vanishingIdeal k C) ev hker
  have hφ : Function.Injective φ.toLinearMap := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.2 fun v hv => congrFun (show ev x = 0 from hx) ⟨v, hv⟩
  rw [(Submodule.equivMapOfInjective _ hφ _).finrank_eq, ← Submodule.map_comp]
  rfl

theorem eval_eq_zero_of_hilb_le : (∀ (k : Type) [Field k] [IsAlgClosed k] (J : Type) [Fintype J] (C : Set (J → k)) (g N : ℕ), (MvPolynomial.vanishingIdeal k C).IsPrime → (MvPolynomial.vanishingIdeal k C).IsHomogeneous (MvPolynomial.homogeneousSubmodule J k) → (∃ i, MvPolynomial.X i ∉ MvPolynomial.vanishingIdeal k C) → ringKrullDim (MvPolynomial J k ⧸ MvPolynomial.vanishingIdeal k C) = (g + 1 : ℕ) → (∀ d, 1 ≤ d → hilb C d ≤ (N * d) ^ g) → ∀ v : J → k, (∀ (d : ℕ) (Pf : MvPolynomial J k), d ≤ N ^ g * g.factorial → Pf.IsHomogeneous d → Pf ∈ MvPolynomial.vanishingIdeal k C → MvPolynomial.eval v Pf = 0) → ∀ Pf ∈ MvPolynomial.vanishingIdeal k C, MvPolynomial.eval v Pf = 0) := by
  intro k _ _ J _ C g N hP hPh hne hdim hb v hv Pf hPf
  by_contra h0
  obtain ⟨d, hd, f, hf, hfd, hfv⟩ :=
    exists_form_degree_le_hilbertDegree_eval_ne_zero hPh hne v ⟨Pf, hPf, h0⟩
  refine hfv (hv d f (hd.trans ?_) hfd hf)
  have hH := isHilbertPoly_idealHilbertPoly hPh
  have hg : (idealHilbertPoly (MvPolynomial.vanishingIdeal k C)).natDegree = g := by
    rw [ProjCut.ringKrullDim_eq_natDegree_idealHilbertPoly hPh hne] at hdim
    have := Nat.cast_injective hdim
    omega
  have h1 : 0 ≤ (Polynomial.C ((N : ℚ) ^ g) * Polynomial.X ^ g -
      idealHilbertPoly (MvPolynomial.vanishingIdeal k C)).coeff g := by
    apply coeff_nonneg_of_eventually_eval_nat
    · refine (Polynomial.degree_sub_le _ _).trans (max_le (Polynomial.degree_C_mul_X_pow_le _ _) ?_)
      exact Polynomial.degree_le_of_natDegree_le hg.le
    · filter_upwards [tendsto_natCast_atTop_atTop.eventually hH.eventually_eq,
        Filter.eventually_ge_atTop 1] with n hn h1n
      have := hb n h1n
      rw [hilb_eq_finrank_quotPiece, mul_pow] at this
      rw [Int.cast_natCast] at hn
      rw [Polynomial.eval_sub, Polynomial.eval_C_mul, Polynomial.eval_pow, Polynomial.eval_X,
        ← hn, sub_nonneg]
      exact_mod_cast this
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, _root_.mul_one,
    sub_nonneg] at h1
  have h2 := cast_hilbertDegree hPh
  rw [Polynomial.leadingCoeff, hg] at h2
  have h3 : (hilbertDegree (MvPolynomial.vanishingIdeal k C) : ℚ) ≤ (N : ℚ) ^ g * g.factorial := by
    rw [h2, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
  exact_mod_cast h3

end GlobalTheory.ZH
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.DegreeFormsDimensionAbelianConeLe

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianFormCount

theorem hilb_cone_le_of_span {K : Type} [Field K] {X : Scheme.{0}} (p : X ⟶ Sp K) (L : LB X) (N d m : ℕ)
    {J : Type} [Finite J] (s : J → (lbPow L N).Sec) (b : Fin m → (lbPow L (N * d)).Sec)
    (hb : ∀ t : (lbPow L (N * d)).Sec, ∃ a : Fin m → K, ∀ j, t.f j = ∑ i, constFn p _ (a i) * (b i).f j) :
    hilb (cone p (lbPow L N) s) d ≤ m := by
  have hC : ∀ v : cone p (lbPow L N) s, ∃ (x : Sp K ⟶ X) (l : PUnit → L.ι) (c : K) (_ : x ≫ p = 𝟙 _)
      (h : ⊤ ≤ x ⁻¹ᵁ SectionRing.chart L l),
      ∀ j, v.1 j = TorsionZero.val x _ h ((s j).f l) * c := by
    rintro ⟨v, x, hx, l, c, hl, hv⟩
    exact ⟨x, l, c, hx, hl, fun j => (hv j).trans ((_root_.mul_comm _ _).trans
      (congrArg (· * (c : K)) (dif_pos hl)))⟩
  choose x l c hx hl hv using hC
  let β : Fin m → cone p (lbPow L N) s → K := fun i v =>
    TorsionZero.val (x v) _ (hl v) ((b i).f (l v)) * c v ^ d
  have le : (MvPolynomial.homogeneousSubmodule J K d).map
      (LinearMap.pi fun v : cone p (lbPow L N) s => (MvPolynomial.aeval (R := K) v.1).toLinearMap) ≤
      Submodule.span K (Set.range β) := by
    rintro _ ⟨F, hF, rfl⟩
    have hm := TorsionZero.aeval_mem_of_isHomogeneous (SectionRing.secs p L)
      (x := fun j => (SectionRing.secEquiv p L N (s j) : SectionRing.Fam p L))
      (fun j => (SectionRing.secEquiv p L N (s j)).2) hF
    obtain ⟨a, ha⟩ := hb ((SectionRing.secEquiv p L (N * d)).symm ⟨_, hm⟩)
    refine (Submodule.mem_span_range_iff_exists_fun K).2 ⟨a, funext fun v => ?_⟩
    let ev : SectionRing.Fam p L →ₐ[K] K :=
      { (TorsionZero.val (x v) _ (hl v)).comp (SectionRing.evalFam p L (l v)) with
        commutes' := fun r => TorsionZero.val_const p (x v) (hx v) _ (hl v) r }
    have h1 : ev (MvPolynomial.aeval (fun j => (SectionRing.secEquiv p L N (s j) : SectionRing.Fam p L)) F) =
        ∑ i, a i * TorsionZero.val (x v) _ (hl v) ((b i).f (l v)) :=
      (congrArg (TorsionZero.val (x v) _ (hl v)) (ha (l v))).trans ((map_sum _ _ _).trans
        (Finset.sum_congr rfl fun i _ => (map_mul _ _ _).trans
          (congrArg (· * _) (TorsionZero.val_const p (x v) (hx v) _ (hl v) (a i)))))
    rw [MvPolynomial.comp_aeval_apply] at h1
    change _ = MvPolynomial.aeval v.1 F
    rw [show v.1 = _ from funext (hv v), TorsionZero.aeval_mul_of_isHomogeneous _ _ hF]
    refine Eq.trans ?_ (congrArg (· * c v ^ d) h1).symm
    rw [Finset.sum_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (_root_.mul_assoc _ _ _).symm
  have := Module.Finite.span_of_finite K (Set.finite_range β)
  exact (Submodule.finrank_mono le).trans ((finrank_range_le_card β).trans (Fintype.card_fin m).le)

theorem hilb_cone_le : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ) (J : Type) [Fintype J] (s : J → (lbPow P.L N).Sec) (d : ℕ), 1 ≤ N → 1 ≤ d → hilb (cone P.A.hom (lbPow P.L N) s) d ≤ (N * d) ^ P.g := by
  intro h K _ _ P N J _ s d hN hd
  obtain ⟨b, hb⟩ := PowSec.exists_basis_sections h.globalSectionsRank K P (N * d) (Nat.mul_pos hN hd)
  exact hilb_cone_le_of_span P.A.hom P.L N d _ s b fun t => (hb t).exists

end GlobalTheory.AbelianFormCount
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.MemVanishingIdealOfFormVanishingTorsionStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.mem_vanishingIdeal_of_form_vanishing_torsion : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N d k : ℕ) (J : Type) (s : J → (lbPow P.L N).Sec) (F : MvPolynomial J K), 4 ≤ N → (k : K) ≠ 0 → N ^ P.g * P.g.factorial * d < k ^ 2 → F.IsHomogeneous d → (∀ x : (Out.baseOver (Sp K)) ⟶ P.A, x ^ k = 1 → ∃ v : J → K, Crd (lbPow P.L N) s (x.left : Sp K ⟶ P.A.left) v ∧ MvPolynomial.eval v F = 0) → F ∈ MvPolynomial.vanishingIdeal K (cone P.A.hom (lbPow P.L N) s) := by
  first | exact @GlobalTheory.TorsionForm.mem_vanishingIdeal_of_vanish_on_torsion | exact GlobalTheory.TorsionForm.mem_vanishingIdeal_of_vanish_on_torsion | (intros; apply GlobalTheory.TorsionForm.mem_vanishingIdeal_of_vanish_on_torsion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaPointDeterminesPolarisedLevel

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ThetaDet

theorem cone_subset (h : Out.Laws) {K : Type} [Field K] [IsAlgClosed K] (P P' : Out.PolAV (Sp K)) {g N k : ℕ}
    (hg : P.g = g) (hg' : P'.g = g) (hN : 4 ≤ N) (hk : (k : K) ≠ 0) (hb : N ^ g * g.factorial < k) {J : Type}
    [Fintype J] {s : J → (lbPow P.L N).Sec} {s' : J → (lbPow P'.L N).Sec}
    (hs : ImmBy P.A.hom _ s Set.univ) (hs' : ImmBy P'.A.hom _ s' Set.univ)
    (hx : ∀ x : Out.baseOver (Sp K) ⟶ P'.A, x ^ k = 1 →
      ∃ v : J → K, Crd (lbPow P'.L N) s' (x.left : Sp K ⟶ P'.A.left) v ∧ v ∈ cone P.A.hom _ s) :
    cone P'.A.hom _ s' ⊆ cone P.A.hom _ s := by
  intro w hw
  have hLB : (lbPow P.L N).IsLB := isLB_lbPow P.isLB N
  have hsm : SmoothOfRelativeDimension g P.A.hom := by
    rw [← hg]
    exact P.smoothDim
  obtain ⟨hpr, hhom, hX, hdim⟩ := ZH.ConePrime.isPrime_vanishingIdeal_cone K P.A.left P.A.hom (lbPow P.L N) J s
    Set.univ hLB hs (polAV_isIntegral_of_isAlgClosed K P) g hsm
  have hnz : ∃ i ∈ (Set.univ : Set J), w i ≠ 0 := by
    obtain ⟨x, -, hxw⟩ := hw
    have h1 : ⊤ ≤ x ⁻¹ᵁ (⨆ i ∈ (Set.univ : Set J), Out.nonzeroLocus (s' i)) := by
      rw [hs'.1]
      simp
    simp only [Set.mem_univ, iSup_pos] at h1
    have h2 := (ZH.CrdCalc.top_le_iff x _).1 h1
    rw [TopologicalSpace.Opens.mem_iSup] at h2
    obtain ⟨i, hi⟩ := h2
    exact ⟨i, Set.mem_univ _, ((ZH.CrdCalc.crd_isUnit_iff i hxw).2 ((ZH.CrdCalc.top_le_iff x _).2 hi)).ne_zero⟩
  refine ZH.ConeClosed.mem_cone_of_vanishing K P.A.left P.A.hom (lbPow P.L N) J s Set.univ hLB hs w hnz ?_
  intro Pf hPf
  refine ZH.eval_eq_zero_of_hilb_le K J _ g N hpr hhom hX hdim ?_ w ?_ Pf hPf
  · intro d hd
    have := AbelianFormCount.hilb_cone_le h K P N J s d (by omega) hd
    rwa [hg] at this
  · intro d F hd hF hFI
    have hFI' : F ∈ MvPolynomial.vanishingIdeal K (cone P'.A.hom (lbPow P'.L N) s') := by
      refine T.mem_vanishingIdeal_of_form_vanishing_torsion h K P' N d k J s' F hN hk ?_ hF ?_
      · rw [hg']
        calc N ^ g * g.factorial * d ≤ N ^ g * g.factorial * (N ^ g * g.factorial) := Nat.mul_le_mul_left _ hd
          _ < k * k := Nat.mul_self_lt_mul_self hb
          _ = k ^ 2 := (sq k).symm
      · intro x hx1
        obtain ⟨v, hv, hvC⟩ := hx x hx1
        exact ⟨v, hv, MvPolynomial.mem_vanishingIdeal_iff.1 hFI v hvC⟩
    exact MvPolynomial.mem_vanishingIdeal_iff.1 hFI' w hw

theorem levelPoint_zero {S : Scheme.{0}} {P : Out.PolAV S} {M : ℕ} {ze : Γ(S, ⊤)ˣ} (lev : Out.Level P M ze) {g : ℕ}
    (hg : P.g = g) : levelPoint lev hg 0 = 1 := by
  rw [ThetaPtDet.levelPoint_eq]
  simp [ReciprocityTheory.ChartRestriction.G.Out.linComb]

theorem levelPoint_single {S : Scheme.{0}} {P : Out.PolAV S} {M : ℕ} {ze : Γ(S, ⊤)ˣ} (lev : Out.Level P M ze) {g : ℕ}
    (hg : P.g = g) (i : Fin (2 * g)) : levelPoint lev hg (Pi.single i 1) = levelBasis lev hg i := by
  rw [ThetaPtDet.levelPoint_eq, ReciprocityTheory.ChartRestriction.G.Out.linComb, List.prod_ofFn,
    Finset.prod_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
  have ht : levelBasis lev hg i ^ M = 1 := lev.torsion _
  rw [Pi.single_eq_same, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 ht, pow_one]

theorem exists_embedding (h : Out.Laws) {g m r N N' : ℕ} (hN : N = m ^ 2) (hN' : N' = r * m) (h4 : 4 ≤ N) {K : Type}
    [Field K] [IsAlgClosed K] (hK : (N' : K) ≠ 0) [NeZero (N' ^ 2)] (P : Out.PolAV (Sp K)) (hg : P.g = g)
    {ze : Γ((Out.baseOver (Sp K)).left, ⊤)ˣ} (lev : Out.Level P (N' ^ 2) ze)
    {v : (Fin (2 * g) → ZMod (N' ^ 2)) → Γ((Out.baseOver (Sp K)).left, ⊤)}
    (hv : Out.IsThetaPt P N' (levelPoint lev hg) v) :
    ∃ (s : (Fin (2 * g) → ZMod (N' ^ 2)) → (lbPow P.L N).Sec) (θ : (lbPow P.L 1).Sec),
      ImmBy P.A.hom _ s Set.univ ∧
      (∀ c, Crd (lbPow P.L N) s ((levelPoint lev hg c ^ N').left : Sp K ⟶ P.A.left)
        fun a => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
          ((ze ^ thetaCoordExp m r a c).val * v (thetaCoordIdx m r a c))) ∧
      (∃ l, θ.f l ≠ 0) ∧ ∀ (y : P.A.left) k l, y ∈ (lbPow P.L N).U k → (Out.mulA P.A m).left y ∈ (lbPow P.L 1).U l →
        Associated (gs (𝟙 P.A.left) y ((lbPow P.L N).U k) ((s 0).f k))
          (gs (Out.mulA P.A m).left y ((lbPow P.L 1).U l) (θ.f l)) := by
  have hodd : Odd N' := hv.1
  obtain ⟨⟨th, t, hth, htf⟩, hform⟩ := (theta_coordinates h g m r N N' hN hN').1 (Sp K) P hg ze lev v hv
  obtain ⟨hcoord, -⟩ := hform th t hth htf
  obtain ⟨-, -, hrest⟩ := (theta_coordinates h g m r N N' hN hN').2 K hodd hK P hg ze lev
  obtain ⟨hspan, -, -⟩ := hrest th t hth htf
  obtain ⟨ρ, e⟩ : ∃ ρ : P.A.left ⟶ (Out.baseOver (Sp K) ⊗ P.A).left,
      ρ ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 P.A.left :=
    ⟨(lift (Over.homMk P.A.hom (by simp [Out.baseOver])) (𝟙 P.A)).left, by rw [← Over.comp_left, lift_snd]; rfl⟩
  obtain ⟨hθ, hassoc⟩ := T.thetaFamily_origin_germ_of_multiplication h K P N m _ (fun a => levelPoint lev hg a ^ r ^ 2) th t ρ e 0 hth htf
    (by rw [levelPoint_zero, one_pow])
  refine ⟨fun a => PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e (N : ℤ) (t a),
    PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((1 : ℕ) : ℤ) th,
    T.isClosedImmersion_of_span_linePowerSections h K P N _ t ρ e h4 hspan, ?_, hθ, hassoc⟩
  intro c
  obtain ⟨u, hu⟩ := hcoord c _ (DVR.exists_gen_of_local (V := K) P.L P.isLB _ _).choose_spec
  have hc := T.homogeneousCoords_of_isValueAt_frame K P N _ t ρ e (levelPoint lev hg c ^ N') _ _ hu
  set φ := CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of K)).hom with hφ
  have hu1 : φ ((u⁻¹ : Γ((Out.baseOver (Sp K)).left, ⊤)ˣ) : Γ((Out.baseOver (Sp K)).left, ⊤)) * φ (u : Γ((Out.baseOver (Sp K)).left, ⊤)) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  convert ZH.CrdCalc.crd_smul (Units.map φ.toMonoidHom u⁻¹) hc using 1
  ext a
  simp only [Units.coe_map, Units.val_mul, map_mul]
  linear_combination (-(φ ((ze ^ thetaCoordExp m r a c : Γ((Out.baseOver (Sp K)).left, ⊤)ˣ) : Γ((Out.baseOver (Sp K)).left, ⊤)) * φ (v (thetaCoordIdx m r a c)))) * hu1

end GlobalTheory.ThetaDet

namespace GlobalTheory


open ThetaDet in
theorem thetaPt_determines : Out.Laws → ThetaPtDeterminesSt := by
  intro h g n k j N N' hn hodd hk hN hN' hb K _ _ hn0 P P' hg hg' ze lev lev' v hv hv'
  haveI := P.isAb
  haveI := P'.isAb
  haveI : IsProper P.A.hom := IsAbelianScheme.proper
  haveI : IsProper P'.A.hom := IsAbelianScheme.proper
  haveI : AlgebraicGeometry.IsIntegral P.A.left := polAV_isIntegral_of_isAlgClosed K P
  haveI : AlgebraicGeometry.IsIntegral P'.A.left := polAV_isIntegral_of_isAlgClosed K P'
  have hN'' : N' = n ^ j * n ^ k * n ^ k := by rw [hN', hN]; ring
  have hn3 : 3 ≤ n := by
    have h2 := hn.two_le
    have hne : n ≠ 2 := by
      rintro rfl
      exact (by decide : ¬ Odd 2) hodd
    omega
  have h4 : 4 ≤ N := by
    have h1 : 3 ≤ n ^ k := le_trans hn3 (Nat.le_self_pow (by omega) n)
    rw [hN]
    nlinarith
  have hK : ((N' : ℕ) : K) ≠ 0 := by
    rw [hN'']
    push_cast
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hn0) (pow_ne_zero _ hn0)) (pow_ne_zero _ hn0)
  have hN'0 : N' ≠ 0 := by
    rintro h0
    rw [h0, Nat.cast_zero] at hK
    exact hK rfl
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero 2 hN'0⟩
  have hoddN' : Odd N' := hv.1
  obtain ⟨s, θ, hs, hcrd, hθ, hass⟩ := ThetaDet.exists_embedding h hN hN'' h4 hK P hg lev hv
  obtain ⟨s', θ', hs', hcrd', hθ', hass'⟩ := ThetaDet.exists_embedding h hN hN'' h4 hK P' hg' lev' hv'
  have hcone1 : cone P'.A.hom _ s' ⊆ cone P.A.hom _ s := by
    refine ThetaDet.cone_subset h P P' hg hg' h4 hK hb hs hs' ?_
    intro x hx
    obtain ⟨c, rfl⟩ := ((theta_coordinates h g (n ^ k) (n ^ j * n ^ k) N N' hN hN'').2 K hoddN' hK P' hg' ze
      lev').2.1 x |>.1 hx
    exact ⟨_, hcrd' c, _, Over.w _, hcrd c⟩
  have hcone2 : cone P.A.hom _ s ⊆ cone P'.A.hom _ s' := by
    refine ThetaDet.cone_subset h P' P hg' hg h4 hK hb hs' hs ?_
    intro x hx
    obtain ⟨c, rfl⟩ := ((theta_coordinates h g (n ^ k) (n ^ j * n ^ k) N N' hN hN'').2 K hoddN' hK P hg ze
      lev).2.1 x |>.1 hx
    exact ⟨_, hcrd c, _, Over.w _, hcrd' c⟩
  obtain ⟨φ, hφ⟩ := T.exists_iso_of_equal_coordinateCones K P.A P'.A (lbPow P.L N) (lbPow P'.L N) _ s s' (isLB_lbPow P.isLB N)
    (isLB_lbPow P'.isLB N) hs hs' (Set.Subset.antisymm hcone2 hcone1)
  have heq : ∀ c, (levelPoint lev hg c ^ N') ≫ φ.hom = levelPoint lev' hg' c ^ N' := by
    intro c
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    exact ZH.ImmSep.eq_of_crd_eq K P'.A.left P'.A.hom (lbPow P'.L N) _ s' Set.univ (isLB_lbPow P'.isLB N) hs' K
      _ _ _ (by rw [Category.assoc, Over.w φ.hom, Over.w, Over.w]) (hφ K _ _ (hcrd c)) (hcrd' c)
  have hη : η ≫ φ.hom = η := by
    have h0 := heq 0
    rw [ThetaDet.levelPoint_zero, ThetaDet.levelPoint_zero, one_pow, one_pow] at h0
    have e1 : (1 : Out.baseOver (Sp K) ⟶ P.A) = η := Over.OverMorphism.ext rfl
    have e2 : (1 : Out.baseOver (Sp K) ⟶ P'.A) = η := Over.OverMorphism.ext rfl
    rw [e1, e2] at h0
    exact h0
  haveI hmon : IsMonHom φ.hom := h.rigidity (Sp K) P.A P'.A P.isAb P'.isAb φ.hom hη
  have hLBiso := T.lbIso_pull_of_hom_preserving_coordinates h K P P' N (n ^ k) _ s s' 0 θ θ' φ.hom
    (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (by omega))) hmon
    (by simpa only [Set.mem_univ, iSup_pos] using hs.1) (fun F _ y w hw => hφ F y w hw) hθ hass hass'
  have hpol : IsPolIso P P' φ := ⟨hmon, hLBiso⟩
  obtain ⟨lev'', hb'', hv''⟩ := T.exists_level_thetaPt_of_polarisedIso h g N' K P P' hg hg' φ hpol ze lev' v hv'
  have hnv := T.thetaPt_support_meets_every_coset h g n N' hn.two_le (by rw [hN'']; exact Dvd.dvd.mul_left (pow_dvd_pow n hk) _) K P hg ze
    lev v hv
  have hpowN : N' = n ^ (j + 2 * k) := by rw [hN'']; ring
  have hpw : ∀ i, levelBasis lev hg i ^ N' = levelBasis lev'' hg i ^ N' := by
    intro i
    apply (cancel_mono φ.hom).1
    rw [pow_comp, pow_comp, hb'' i, ← pow_comp, ← ThetaDet.levelPoint_single lev hg i, heq,
      ThetaDet.levelPoint_single]
  refine ⟨φ, hpol, fun i => ?_⟩
  rw [T.levelBasis_eq_of_same_thetaPt h g n (j + 2 * k) N' hodd hpowN K P hg ze lev lev'' v hv hv'' hpw hnv i, hb'' i]

end GlobalTheory
end
end
end
