module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
public import Development.WeilBound.CoreStatements.HodgeTatePoints.A12
public import Development.WeilBound.CoreStatements.HodgeTatePoints.A28
public import Development.WeilBound.CoreStatements.HodgeTatePoints.A36
public import Development.WeilBound.CoreStatements.HodgeTatePoints.A53
import Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsAmpleBaseLocalizationEq
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockComp
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraTer
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerAlt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreAlt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisExtra
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestTer
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastExtra
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraLast
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import Mathlib.Algebra.Group.End
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic.Continuity
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fintype.Defs
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumSymm
import Mathlib.Tactic.ReduceModChar
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Fintype
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraExtra
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherExtra
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGraphClosed
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
import Mathlib.RingTheory.RegularLocalRing.Defs
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSide
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTer
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZpowMemSubringOfInvMem
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.KleimanNefF

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutByFormField

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace CutByFormField

theorem vecCons_comp_finRotate {α : Type*} {n : ℕ} (c : α) (bs : Fin n → α) :
    Matrix.vecCons c bs ∘ finRotate (n + 1) = Fin.snoc (α := fun _ => α) bs c := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp
  · rw [Function.comp_apply, finRotate_apply, Fin.coeSucc_eq_succ, Fin.snoc_castSucc,
      Matrix.cons_val_succ]

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

end CutByFormField

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.WeilNumbersImpVerticalDivisorsCommute

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace VerticalDivisorsCommuting

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem intNum_snoc {F : Type u} [Field F] (V : Ideal (MRing ι F)) {n : ℕ} (L : Fin n → K → ℤ)
    (b : K → ℤ) :
    intNum F V (Fin.snoc (α := fun _ => K → ℤ) L b) = intNum F V (Matrix.vecCons b L) := by
  rw [← CutByFormField.vecCons_comp_finRotate]
  exact FieldNumbers.IntNumSymm.proof F K ι V (n + 1) _ _

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

end VerticalDivisorsCommuting

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsNeZeroOfIsSubvar

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Filter
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

theorem SectionCount.bound_from_one {X : ℝ} {d : ℕ} {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤ f n) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤ f n := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hC
  refine ⟨max C (|X| * (n₀ : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)), fun n hn => ?_⟩
  have hnd : (1 : ℝ) ≤ (n : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hn)
  have hfac : (0 : ℝ) < ((d + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rcases le_or_gt n₀ n with h | h
  · have h1 := hn₀ n h
    have h2 : C * (n : ℝ) ^ d ≤ max C (|X| * (n₀ : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)) * (n : ℝ) ^ d :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    linarith
  · have hX : X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) ≤
        |X| * (n₀ : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) := by
      apply div_le_div_of_nonneg_right _ hfac.le
      calc X * (n : ℝ) ^ (d + 1) ≤ |X| * (n : ℝ) ^ (d + 1) :=
            mul_le_mul_of_nonneg_right (le_abs_self X) (by positivity)
        _ ≤ |X| * (n₀ : ℝ) ^ (d + 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by exact_mod_cast h.le) _)
              (abs_nonneg X)
    have hM := le_max_right C (|X| * (n₀ : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ))
    have hM0 : 0 ≤ max C (|X| * (n₀ : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)) :=
      le_trans (by positivity) hM
    have h3 := le_mul_of_one_le_right hM0 hnd
    linarith [hf n]

theorem SectionCount.exists_ne_zero_of_isSubvar {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} {e : ℕ} (h : Kleiman.IsSubvar x (Kleiman.primeOf (S := k) x) e) : ∃ i, x i ≠ 0 := by
  obtain ⟨i, hi⟩ := h.relevant
  refine ⟨i, fun h0 => hi ?_⟩
  rw [Kleiman.primeOf, ReciprocityTheory.ChartRestriction.G.Geo.coordIdeal, RingHom.mem_ker]
  simp [ReciprocityTheory.ChartRestriction.G.Geo.coneMap, h0]

theorem SectionCount.transfer (hBase : BaseRealises.Statement)
    (hP : PowRealises.Statement) (hN : NumModel.Statement)
    (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω) (hx : x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)
    (hmod : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀) (Q : Kleiman.LineBundle F x) (ν : K → ℤ)
    (hQ : BundleRealises y k₀ Q ν) (d q : ℕ) (hsub : Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) (d + 1)) :
    ((Kleiman.interNum (Kleiman.primeOf (S := F) x) (fun _ : Fin (d + 1) => Q.toSubSystem) -
        ((d + 1 : ℕ) : ℤ) * Kleiman.interNum (Kleiman.primeOf (S := F) x)
          (Fin.cons (α := fun _ => Kleiman.SubSystem F x Ω) (Kleiman.twistSys F x (q : ℤ))
            (fun _ : Fin d => Q.toSubSystem)) : ℤ) : ℝ) =
      (NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => ν) : ℝ) -
        ((d + 1 : ℕ) : ℝ) * (NumbersDVR.intNum F (mIdealOver F y)
          (Fin.snoc (α := fun _ => K → ℤ) (fun _ : Fin d => ν) (q • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) : ℝ) ∧
    ∀ n : ℕ, (Kleiman.twistMul Q.toSubSystem n (-((n : ℤ) * q))).secs =
      secOver F y (n • (ν - q • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) := by
  have h1 : Kleiman.interNum (Kleiman.primeOf (S := F) x) (fun _ : Fin (d + 1) => Q.toSubSystem) =
      NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => ν) :=
    hN F K ι Ω y k₀ N e x hx hmod (d + 1) (fun _ => Q) (fun _ => ν) (fun _ => hQ) hsub
  have hqs : ((q : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) = q • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ := by
    funext j; simp
  have hL : (fun i => (Fin.cons (α := fun _ => Kleiman.LineBundle F x) (Kleiman.twistBundle F x (q : ℤ))
      (fun _ : Fin d => Q) i).toSubSystem) =
      Fin.cons (α := fun _ => Kleiman.SubSystem F x Ω) (Kleiman.twistSys F x (q : ℤ))
        (fun _ : Fin d => Q.toSubSystem) := by
    funext i
    refine Fin.cases rfl (fun _ => rfl) i
  have h2 : Kleiman.interNum (Kleiman.primeOf (S := F) x)
      (Fin.cons (α := fun _ => Kleiman.SubSystem F x Ω) (Kleiman.twistSys F x (q : ℤ))
        (fun _ : Fin d => Q.toSubSystem)) =
      NumbersDVR.intNum F (mIdealOver F y)
        (Fin.snoc (α := fun _ => K → ℤ) (fun _ : Fin d => ν) (q • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) := by
    rw [NumbersDVR.VerticalDivisorsCommuting.intNum_snoc, ← hL, ← hqs]
    exact hN F K ι Ω y k₀ N e x hx hmod (d + 1) _ (Fin.cons ((q : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) fun _ => ν)
      (fun i => Fin.cases (hBase F K ι Ω y k₀ N e x hx hmod (q : ℤ)) (fun _ => hQ) i) hsub
  refine ⟨by rw [h1, h2]; push_cast; ring, fun n => ?_⟩
  rw [hP F K ι Ω y k₀ N e x hx hmod Q ν hQ n (-((n : ℤ) * q))]
  congr 1
  funext j
  simp only [smul_eq_mul, nsmul_eq_mul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.natCast_apply]
  ring

theorem SectionCount.equiv (hG : GraphModel.Statement) (hB : BundleOfDeg.Statement) (hD : ModelDim.Statement)
    (hBase : BaseRealises.Statement) (hP : PowRealises.Statement) (hV : VeryAmpleModel.Statement)
    (hN : NumModel.Statement) :
    Kleiman.SectionCount.Statement.{0, 0} ↔ IndefiniteRowSideFullHecke.Kleiman2.SectionCount.Statement := by
  constructor
  · intro hA F _ K _ _ ι _ Ω _ _ y k₀ d ν q hmod hdim hva hq
    have hpos : 0 < Fintype.card (ι k₀) := by
      obtain ⟨i, -⟩ := hmod.1 k₀
      exact Fintype.card_pos_iff.2 ⟨i⟩
    obtain ⟨N, hN'⟩ : ∃ N, Fintype.card (ι k₀) = N + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    obtain ⟨e⟩ : Nonempty (ι k₀ ≃ Fin (N + 1)) := ⟨(Fintype.equivFin _).trans (finCongr hN')⟩
    obtain ⟨Q, hQ⟩ := hB F K ι Ω y k₀ N e hmod ν
    have hsub := (hD F K ι Ω y k₀ N e _ rfl hmod (d + 1)).2 hdim
    have hvaQ := (hV F K ι Ω y k₀ N e _ rfl hmod Q ν hQ).2 hva
    obtain ⟨hZ, hS⟩ := SectionCount.transfer hBase hP hN F K ι Ω y k₀ N e _ rfl hmod Q ν hQ d q hsub
    obtain ⟨C, hC⟩ := hA F Ω N _ d Q q hsub hvaQ hq
    refine SectionCount.bound_from_one (fun n => Nat.cast_nonneg _) ⟨C, hC.mono fun n hn => ?_⟩
    rw [← hZ, ← hS n]
    exact hn
  · intro hB' k _ Ω _ _ N x d Nb b hsub hva hb
    obtain ⟨r, h, hby⟩ := hva
    have hgen : IsGraphGen Nb 0 h := fun I => by
      rw [Kleiman.SubSystem.twist_twistSys_zero]
      exact hby.generates I
    have hmod := hG k N Ω x Nb 0 (r + 1) h (SectionCount.exists_ne_zero_of_isSubvar hsub) hgen
    have hQ := realises_graph Nb 0 h hgen
    have hdim := (hD k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x h) baseBlock N (Equiv.refl _) x rfl
      hmod (d + 1)).1 hsub
    have hvaB := (hV k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x h) baseBlock N (Equiv.refl _) x rfl
      hmod Nb (graphDeg 0) hQ).1 ⟨r, h, hby⟩
    obtain ⟨hZ, hS⟩ := SectionCount.transfer hBase hP hN k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω
      (graphVec x h) baseBlock N (Equiv.refl _) x rfl hmod Nb (graphDeg 0) hQ d b hsub
    obtain ⟨C, hC⟩ := hB' k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x h) baseBlock d (graphDeg 0) b
      hmod hdim hvaB hb
    refine ⟨C, eventually_atTop.2 ⟨1, fun n hn => ?_⟩⟩
    rw [hZ, hS n]
    exact hC n hn

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsNeZeroOfIsSubvarAlt

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

theorem exists_ne_zero_of_isSubvar {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} {d : ℕ} (h : Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) d) : ∃ i, x i ≠ 0 := by
  obtain ⟨i, hi⟩ := h.relevant
  refine ⟨i, fun h0 => hi ?_⟩
  change MvPolynomial.X i ∈ RingHom.ker (ReciprocityTheory.ChartRestriction.G.Geo.coneMap F x)
  rw [RingHom.mem_ker]
  simp [ReciprocityTheory.ChartRestriction.G.Geo.coneMap, h0]

theorem VeryAmpleNefPlusAmple.equiv (hBun : BundleOfDeg.Statement) (hNef : ModelNefEq.Statement)
    (hVA : ModelVeryAmpleEq.Statement) (hDim : ModelDimEq.Statement) :
    Kleiman.VeryAmpleNefPlusAmple.Statement.{0, 0} ↔ IndefiniteRowSideFullHecke.Kleiman2.VeryAmpleNefPlusAmple.Statement := by
  constructor
  · intro hA d F _ K _ _ ι _ Ω _ _ y k₀ hmod hdim μ hnef t ht
    obtain ⟨i₀, -⟩ := hmod.1 k₀
    have hpos : 0 < Fintype.card (ι k₀) := Fintype.card_pos_iff.mpr ⟨i₀⟩
    let e : ι k₀ ≃ Fin (Fintype.card (ι k₀) - 1 + 1) :=
      (Fintype.equivFin _).trans (finCongr (Nat.succ_pred_eq_of_pos hpos).symm)
    obtain ⟨Q, hQ⟩ := hBun F K ι Ω y k₀ _ e hmod μ
    have hs := (hDim F K ι Ω y k₀ _ e hmod d).mpr hdim
    have hn := (hNef F K ι Ω y k₀ _ e hmod μ Q hQ).mpr hnef
    obtain ⟨p, m, hp, hm, hva⟩ := hA F d Ω _ _ Q hs hn t ht
    exact ⟨p, m, hp, hm, (hVA F K ι Ω y k₀ _ e hmod μ Q hQ p m hp).mp hva⟩
  · intro hB k _ d Ω _ _ N x M hs hnef t ht
    have hx := exists_ne_zero_of_isSubvar hs
    obtain ⟨n, hn⟩ := Generated.full.{0, 0} k Ω N x M
    obtain ⟨r, g, -, hg⟩ := GraphClosedAlt.exists_fin_generators
      (M.tensorProd (twistBundle k x n)) (hn n le_rfl)
    have hgen : IsGraphGen M n g := hg
    have hmod := GraphModel.full k N Ω x M n (r + 1) g hx hgen
    have hsec := twist_secs_eq_secOver M n g hgen
    have hdim := (hDim k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x g) baseBlock N (Equiv.refl _)
      hmod d).mp hs
    have hnef' := (hNef k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x g) baseBlock N (Equiv.refl _)
      hmod (graphDeg n) M hsec).mp hnef
    obtain ⟨a, m, ha, hm, hva⟩ := hB d k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x g) baseBlock hmod hdim
      (graphDeg n) hnef' t ht
    exact ⟨a, m, ha, hm, (hVA k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x g) baseBlock N (Equiv.refl _)
      hmod (graphDeg n) M hsec a m ha).mpr hva⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
end

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.KTwins

section

@[expose] public section

namespace PositivityTheory.HtPt.Ktw

theorem a64 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.NefProductNonneg.Statement :=
  GroundTheory.Heights₂.Heights.ForSecondHalf.NefProductNonneg.unfolding_matrix_of_form a28 (a63 hR)

theorem a73 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.VeryAmpleNefPlusAmple.Statement :=
  (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.VeryAmpleNefPlusAmple.equiv
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.BundleOfDeg.full a65 a71
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelDimEq.full).mp (a72 hR)

theorem a77 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.SectionCount.Statement := (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.SectionCount.equiv
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.GraphModel.full
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.BundleOfDeg.full
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelDim.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.BaseRealises.proof a66
    (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.VeryAmpleModel.proof
      PositivityTheory.HtPt.KtwS.SectionsOverLocalization.VeryAmpleEq.full a69) a18).mp
    (GroundTheory.Heights₂.Heights.Kleiman.SectionCount.assembled a39 a43 a48 a51 hR)

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2 in
theorem k_twins : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0} → NefProductNonneg.Statement ∧ VeryAmpleNefPlusAmple.Statement ∧ SectionCount.Statement :=
  fun hR => ⟨a64 hR, a73 hR, a77 hR⟩

end PositivityTheory.HtPt.Ktw
end
end
