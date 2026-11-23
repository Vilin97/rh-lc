module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagGrassPush
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagGrassSteps
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPointsIntegralProductFormulaStatement
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Assembly
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagArithVar
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagGrassPush
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagImageGrass
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFsInvPow
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHFlProdLinear
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmAExpand
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ChangeOfModel
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsPermAppendSnoc

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem exists_perm_append_snoc {α : Type*} {d r : ℕ} (A : Fin d → α) (B : Fin r → α) (c : α)
    (h : d + r + 1 = d + 1 + r) :
    ∃ σ : Equiv.Perm (Fin (d + r + 1)),
      ((Fin.append (Fin.snoc (α := fun _ => α) A c) B) ∘ Fin.cast h) ∘ σ =
        Fin.snoc (α := fun _ => α) (Fin.append A B) c := by
  let g : ℕ → ℕ := fun i => if i < d then i else if i = d + r then d else i + 1
  have hg : ∀ i, i < d + r + 1 → g i < d + r + 1 := by
    intro i hi
    simp only [g]
    split_ifs <;> omega
  let f : Fin (d + r + 1) → Fin (d + r + 1) := fun i => ⟨g i, hg i i.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hab' : g a = g b := congrArg Fin.val hab
    have ha := a.2
    have hb := b.2
    apply Fin.ext
    simp only [g] at hab'
    split_ifs at hab' <;> omega
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf), ?_⟩
  funext j
  simp only [Function.comp, Equiv.ofBijective_apply]
  induction j using Fin.lastCases with
  | last =>
    have e : Fin.cast h (f (Fin.last (d + r))) = Fin.castAdd r (Fin.last d) := by
      apply Fin.ext
      simp [f, g]
    rw [e, Fin.append_left, Fin.snoc_last, Fin.snoc_last]
  | cast j =>
    rw [Fin.snoc_castSucc]
    induction j using Fin.addCases with
    | left i =>
      have e : Fin.cast h (f (Fin.castSucc (Fin.castAdd r i))) = Fin.castAdd r (Fin.castSucc i) := by
        apply Fin.ext
        simp [f, g]
      rw [e, Fin.append_left, Fin.append_left, Fin.snoc_castSucc]
    | right i =>
      have e : Fin.cast h (f (Fin.castSucc (Fin.natAdd d i))) = Fin.natAdd (d + 1) i := by
        apply Fin.ext
        have := i.2
        simp [f, g]
        split_ifs <;> omega
      rw [e, Fin.append_right, Fin.append_right]

theorem isSmoothHerm_constLine {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (c : ℝ) :
    IsSmoothHerm (ReciprocityTheory.ChartRestriction.G.AI.I2.constLine c : HermLine ι) :=
  show ContDiffOn ℝ _ (fun _ => Real.exp (-c)) _ from contDiffOn_const

theorem isPullHerm_constLine {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (c : ℝ) :
    IsPullHerm κ v (ReciprocityTheory.ChartRestriction.G.AI.I2.constLine c : HermLine ι) (ReciprocityTheory.ChartRestriction.G.AI.I2.constLine c) := by
  refine ⟨?_, fun _ => rfl⟩
  funext k'
  show (0 : K' → ℤ) k' = Function.extend κ (0 : K → ℤ) 0 k'
  classical
  rw [Function.extend_def]
  split_ifs <;> rfl

theorem ptsIntegral_projection : PFStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d r : ℕ) (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ)) (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin r → HermLine ι'), IsBlockMap κ v → IsArithVar P' (d + r + 1) → IsArithVar (imageZ v P') (d + 1) → IsFieldIntersection J → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) → ptsIntegral P' (pot (Fin.append L' N)) (fun _ => 1) = (J (fibreIdeal κ G) r (fun j => fibreDeg κ (N j).a) : ℝ) * ptsIntegral (imageZ v P') (pot L) (fun _ => 1) := by
  intro hPF hEx K _ ι _ K' _ ι' _ κ v P' d r G J L L' N hb hP' hZ hJ hL hLL hN
  obtain ⟨I, hI⟩ := hEx
  have hn : d + r + 1 = d + 1 + r := by omega
  have hL' : ∀ j, IsSmoothHerm (L' j) := fun j =>
    GroundTheory.Heights₂.Heights.Inter.IsPullHerm.isSmoothHerm hb (hLL j) (hL j)
  let c : ℝ := -Real.log ((2 : ℕ) : ℝ)
  let cZ : HermLine ι := ReciprocityTheory.ChartRestriction.G.AI.I2.constLine c
  let cZ' : HermLine ι' := ReciprocityTheory.ChartRestriction.G.AI.I2.constLine c
  have hcZ' : IsSmoothHerm cZ' := isSmoothHerm_constLine c
  have hcZ : IsSmoothHerm cZ := isSmoothHerm_constLine c
  have hAN : ∀ j, IsSmoothHerm (Fin.append L' N j) := by
    intro j
    induction j using Fin.addCases with
    | left i => rw [Fin.append_left]; exact hL' i
    | right i => rw [Fin.append_right]; exact hN i

  have hpf := hPF I hI K ι K' ι' κ v P' (d + 1) r G J (Fin.snoc (α := fun _ => HermLine ι) L cZ)
    (Fin.snoc (α := fun _ => HermLine ι') L' cZ') N hb (hn ▸ hP') hZ hJ
    (fun j => by
      induction j using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact hcZ
      | cast i => rw [Fin.snoc_castSucc]; exact hL i)
    (fun j => by
      induction j using Fin.lastCases with
      | last => rw [Fin.snoc_last, Fin.snoc_last]; exact isPullHerm_constLine κ v c
      | cast i => rw [Fin.snoc_castSucc, Fin.snoc_castSucc]; exact hLL i)
    hN

  obtain ⟨σ, hσ⟩ := exists_perm_append_snoc L' N cZ' hn
  have hcast : ∀ {m n : ℕ} (e : n = m) (M : Fin m → HermLine ι'),
      I K' ι' P' m M = I K' ι' P' n (M ∘ Fin.cast e) := by
    intro m n e M
    subst e
    rfl
  have hsmooth : ∀ j, IsSmoothHerm
      ((Fin.append (Fin.snoc (α := fun _ => HermLine ι') L' cZ') N ∘ Fin.cast hn) j) := by
    intro j
    have hall : ∀ i, IsSmoothHerm (Fin.append (Fin.snoc (α := fun _ => HermLine ι') L' cZ') N i) := by
      intro i
      induction i using Fin.addCases with
      | left i =>
        rw [Fin.append_left]
        induction i using Fin.lastCases with
        | last => rw [Fin.snoc_last]; exact hcZ'
        | cast i => rw [Fin.snoc_castSucc]; exact hL' i
      | right i => rw [Fin.append_right]; exact hN i
    exact hall _
  have hleft : I K' ι' P' (d + 1 + r) (Fin.append (Fin.snoc (α := fun _ => HermLine ι') L' cZ') N) =
      I K' ι' P' (d + r + 1) (Fin.snoc (α := fun _ => HermLine ι') (Fin.append L' N) cZ') := by
    rw [hcast hn, ← hσ]
    exact ((hI K' ι').1 P' (d + r + 1) _ σ hP' hsmooth).symm

  have h2 : Nat.Prime 2 := Nat.prime_two
  have hconsL := (GroundTheory.Heights₂.Heights.Inter.Conservation.proof K' ι' (I K' ι') (hI K' ι') P' (d + r)
    (Fin.append L' N) 2 hP' hAN h2).2
  have hconsR := (GroundTheory.Heights₂.Heights.Inter.Conservation.proof K ι (I K ι) (hI K ι) (imageZ v P') d L 2 hZ hL h2).2
  have hlog : Real.log ((2 : ℕ) : ℝ) ≠ 0 := by
    have : (1 : ℝ) < ((2 : ℕ) : ℝ) := by norm_num
    exact (Real.log_pos this).ne'
  rw [hleft] at hpf
  have e1 : Real.log ((2 : ℕ) : ℝ) * ptsIntegral P' (pot (Fin.append L' N)) (fun _ => 1) =
      Real.log ((2 : ℕ) : ℝ) * ((J (fibreIdeal κ G) r (fun j => fibreDeg κ (N j).a) : ℝ) *
        ptsIntegral (imageZ v P') (pot L) (fun _ => 1)) := by
    rw [← hconsL]
    refine hpf.trans ?_
    rw [hconsR]
    ring
  exact mul_left_cancel₀ hlog e1

end GlobalTheory.CompanionTheory.Ar.Giv
end
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVandCount

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

theorem VandCount.card_lt (N : ℕ) :
    (Finset.univ.filter (fun ab : Fin N × Fin N => ab.1 < ab.2)).card = N * (N - 1) / 2 := by
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have h : ∀ b : Fin N, (∑ a : Fin N, if a < b then 1 else 0) = (b : ℕ) := by
    intro b
    rw [← Finset.card_filter, ← Fin.card_Iio b]
    congr 1
    ext a
    simp
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]

theorem VandCount.card_cross (N j : ℕ) (hj : j ≤ N) :
    (Finset.univ.filter (fun ab : Fin N × Fin N => (ab.1 : ℕ) < j ∧ j ≤ (ab.2 : ℕ))).card = j * (N - j) := by
  have h1 : (Finset.univ.filter (fun a : Fin N => (a : ℕ) < j)).card = j := by
    rw [Fin.card_filter_val_lt, min_eq_right hj]
  have h2 : (Finset.univ.filter (fun a : Fin N => j ≤ (a : ℕ))).card = N - j := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
      (fun a : Fin N => (a : ℕ) < j)
    simp only [not_lt, Finset.card_univ, Fintype.card_fin] at this
    omega
  rw [← Finset.univ_product_univ, Finset.filter_product (fun a : Fin N => (a : ℕ) < j)
    (fun b : Fin N => j ≤ (b : ℕ)), Finset.card_product, h1, h2]

theorem VandCount.proof : VandCount.Statement := by
  intro Ψ _ _ N j hj
  unfold dimN vandCount dimFl
  have hc : Fintype.card (VandPair Ψ N j) = Fintype.card Ψ *
      (Finset.univ.filter (fun ab : Fin N × Fin N =>
        ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j))).card := by
    rw [Fintype.card_subtype, ← Finset.card_univ (α := Ψ), ← Finset.card_product, Finset.univ_product_univ.symm,
      Finset.filter_product_right (fun ab : Fin N × Fin N =>
        ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j))]
  have hsplit : (Finset.univ.filter (fun ab : Fin N × Fin N => ab.1 < ab.2)).card =
      (Finset.univ.filter (fun ab : Fin N × Fin N =>
        ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j))).card +
      (Finset.univ.filter (fun ab : Fin N × Fin N => (ab.1 : ℕ) < j ∧ j ≤ (ab.2 : ℕ))).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter
      (fun ab : Fin N × Fin N => ab.1 < ab.2)) (fun ab => ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j)),
      Finset.filter_filter, Finset.filter_filter]
    congr 2
    ext ab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases ha : (ab.1 : ℕ) < j
      · exact ⟨ha, by by_contra hb; exact h2 ⟨fun _ => by omega, fun _ => ha⟩⟩
      · exact absurd ⟨fun h => absurd h ha, fun h => by omega⟩ h2
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, fun h => by have := h.1 h1; omega⟩
  rw [hc, ← VandCount.card_lt, hsplit, VandCount.card_cross N j hj]
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGrassmannPushOfInputs

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Push

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

section Multilinear

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}

theorem snoc_update_fsHerm (c : HermLine ι) (v : Fin n → K → ℤ) (j : Fin n) (d : K → ℤ) :
    (Fin.snoc (α := fun _ => HermLine ι) (fun i => fsHerm ι (Function.update v j d i)) c) =
      Function.update (Fin.snoc (α := fun _ => HermLine ι) (fun i => fsHerm ι (v i)) c) j.castSucc
        (fsHerm ι d) := by
  rw [← Fin.snoc_update]
  congr 1
  funext i
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [Function.update_of_ne h]

theorem isSmooth_snoc_fsHerm {c : HermLine ι} (hc : IsSmoothHerm c) (v : Fin n → K → ℤ)
    (i : Fin (n + 1)) :
    IsSmoothHerm ((Fin.snoc (α := fun _ => HermLine ι) (fun i => fsHerm ι (v i)) c) i) := by
  induction i using Fin.lastCases with
  | last => rw [Fin.snoc_last]; exact hc
  | cast i => rw [Fin.snoc_castSucc]; exact FsInvPow.isSmoothHerm_fsHerm _

theorem snoc_update_add (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) {c : HermLine ι}
    (hc : IsSmoothHerm c) (v : Fin n → K → ℤ) (j : Fin n) (a b : K → ℤ) :
    I P (n + 1) (Fin.snoc (α := fun _ => HermLine ι) (fun i => fsHerm ι (Function.update v j (a + b) i)) c) =
      I P (n + 1) (Fin.snoc (α := fun _ => HermLine ι) (fun i => fsHerm ι (Function.update v j a i)) c) +
        I P (n + 1) (Fin.snoc (α := fun _ => HermLine ι) (fun i => fsHerm ι (Function.update v j b i)) c) := by
  have hL := isSmooth_snoc_fsHerm hc v
  rw [snoc_update_fsHerm, snoc_update_fsHerm, snoc_update_fsHerm,
    Inter.fam_update_eq_snoc hI hP _ hL _ (FsInvPow.isSmoothHerm_fsHerm _),
    Inter.fam_update_eq_snoc hI hP _ hL _ (FsInvPow.isSmoothHerm_fsHerm _),
    Inter.fam_update_eq_snoc hI hP _ hL _ (FsInvPow.isSmoothHerm_fsHerm _)]
  exact FlagHeightMultilinear.I_snoc_fsHerm_add hI hP _ (fun i => hL _) a b

def snocMultilin (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) {c : HermLine ι}
    (hc : IsSmoothHerm c) : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => K → ℤ) ℝ where
  toFun v := I P (n + 1) (Fin.snoc (α := fun _ => HermLine ι) (fun i => fsHerm ι (v i)) c)
  map_update_add' := by
    intro inst v j a b
    have e : inst = instDecidableEqFin n := Subsingleton.elim _ _
    subst e
    exact snoc_update_add hI hP hc v j a b
  map_update_smul' := by
    intro inst v j t a
    have e : inst = instDecidableEqFin n := Subsingleton.elim _ _
    subst e
    let g : (K → ℤ) →+ ℝ := AddMonoidHom.mk'
      (fun a => I P (n + 1) (Fin.snoc (α := fun _ => HermLine ι) (fun i => fsHerm ι (Function.update v j a i)) c))
      (fun a b => snoc_update_add hI hP hc v j a b)
    exact map_zsmul g t a

theorem snocMultilin_apply (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) (v : Fin n → K → ℤ) :
    snocMultilin hI hP (isSmoothHerm_constLine (-Real.log ((2 : ℕ) : ℝ))) v =
      Real.log ((2 : ℕ) : ℝ) * ptsIntegral P (pot fun i => fsHerm ι (v i)) (fun _ => 1) :=
  (Inter.Conservation.proof K ι I hI P n (fun i => fsHerm ι (v i)) 2 hP
    (fun _ => FsInvPow.isSmoothHerm_fsHerm _) Nat.prime_two).2

theorem log_two_ne : Real.log ((2 : ℕ) : ℝ) ≠ 0 :=
  (Real.log_pos (by norm_num)).ne'

theorem pts_fsHerm_sum (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) {α : Type} [Fintype α]
    (ℓ : Fin n → α → ℤ) (x : α → K → ℤ) :
    ptsIntegral P (pot fun i => fsHerm ι (∑ p, ℓ i p • x p)) (fun _ => 1) =
      ∑ r : Fin n → α, (∏ i, (ℓ i (r i) : ℝ)) *
        ptsIntegral P (pot fun i => fsHerm ι (x (r i))) (fun _ => 1) := by
  refine mul_left_cancel₀ log_two_ne ?_

  rw [← snocMultilin_apply hI hP, MultilinearMap.map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MultilinearMap.map_smul_univ _ (fun i => ℓ i (r i)) (fun i => x (r i)), snocMultilin_apply hI hP]
  simp only [RingHom.id_apply, zsmul_eq_mul, Int.cast_prod]
  ring

theorem pts_neg_eq (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) :
    ptsIntegral P (pot fun _ : Fin n => fsHerm ι fun _ => -1) (fun _ => 1) =
      (-1) ^ n * geomDeg P (fsMulti ι) n := by
  have hg : geomDeg P (fsMulti ι) n =
      ptsIntegral P (pot fun _ : Fin n => fsHerm ι fun _ => 1) (fun _ => 1) := by
    unfold geomDeg
    congr 1
    funext _ z
    show Real.log ((fsMulti ι).h z) = Real.log ((fsHerm ι fun _ => 1).h z)
    rw [FsInvPow.fsHerm_h_eq]
    rfl
  rw [hg]
  refine mul_left_cancel₀ log_two_ne ?_
  have e : (fun _ : Fin n => (fun _ => -1 : K → ℤ)) =
      fun i => (fun _ : Fin n => (-1 : ℤ)) i • (fun _ : Fin n => (fun _ => 1 : K → ℤ)) i := by
    funext _ _
    simp
  rw [← snocMultilin_apply hI hP, e, MultilinearMap.map_smul_univ, snocMultilin_apply hI hP]
  simp only [RingHom.id_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin, zsmul_eq_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one]
  ring

end Multilinear

section Forms

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

def flagIntAdd : RootPoly Ψ N →+ ℚ :=
  AddMonoidHom.mk' (flagInt Ψ N) fun a b => by
    unfold flagInt LowerBoundFree.antisym
    simp only [map_add (f := _), smul_add, Finset.sum_add_distrib, MvPolynomial.coeff_add]

theorem flagInt_prod_linForm {d : ℕ} (ℓ : Fin d → Ψ × Fin N → ℤ) :
    flagInt Ψ N (∏ i, LowerBoundFree.linForm Ψ N (ℓ i)) =
      ∑ r : Fin d → Ψ × Fin N, (∏ i, (ℓ i (r i) : ℚ)) * flagInt Ψ N (∏ i, X (r i)) := by
  have h : ∏ i, LowerBoundFree.linForm Ψ N (ℓ i) =
      ∑ r : Fin d → Ψ × Fin N, C (∏ i, (ℓ i (r i) : ℚ)) * ∏ i, (X (r i) : RootPoly Ψ N) := by
    unfold LowerBoundFree.linForm
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]
  rw [h]
  refine (map_sum (flagIntAdd Ψ N) _ _).trans (Finset.sum_congr rfl fun r _ => ?_)
  exact flagInt_C_mul Ψ N _ _

theorem pts_linForms [Nonempty Ψ] (II : IntersectionSystem) (hII : IsIntersectionSystem II) (hN : 2 ≤ N)
    (hB : ∀ w : Fin (dimFl Ψ N) → Ψ × Fin N,
      ptsIntegral (PFl Ψ N) (pot fun r => xLine Ψ N (w r)) (fun _ => 1) =
        ((flagInt Ψ N (∏ r, X (w r)) : ℚ) : ℝ))
    (d : ℕ) (hd : d = dimFl Ψ N) (ℓ : Fin d → Ψ × Fin N → ℤ) :
    ptsIntegral (PFl Ψ N) (pot fun i => linLine Ψ N (ℓ i)) (fun _ => 1) =
      ((flagInt Ψ N (∏ i, LowerBoundFree.linForm Ψ N (ℓ i)) : ℚ) : ℝ) := by
  subst hd
  have hP := FlagArithVar.proof Ψ N hN
  have hI := hII (FlBlock Ψ N) (FlIdx Ψ N)
  have hlin : (fun i => linLine Ψ N (ℓ i)) =
      fun i => fsHerm (FlIdx Ψ N) (∑ p, ℓ i p • xDeg Ψ N p) := by
    funext i
    unfold linLine linDeg
    congr 1
    funext q
    simp [Finset.sum_apply]
  rw [hlin, pts_fsHerm_sum hI hP, flagInt_prod_linForm]
  push_cast
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← hB r]
  rfl

variable (j : ℕ)

def jForms : Fin (dimN Ψ N j + vandCount Ψ N j) → Ψ × Fin N → ℤ :=
  Fin.append (fun _ => muForm Ψ N j) (fun i => vandForm Ψ N j ((Fintype.equivFin (VandPair Ψ N j)).symm i))

theorem prod_jForms :
    ∏ i, LowerBoundFree.linForm Ψ N (jForms Ψ N j i) = muPoly Ψ N j ^ dimN Ψ N j * vandBlocks Ψ N j := by
  rw [Fin.prod_univ_add]
  simp only [jForms, Fin.append_left, Fin.append_right, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    linForm_muForm, prod_vandForm]

theorem linLine_jForms :
    (fun i => linLine Ψ N (jForms Ψ N j i)) =
      Fin.append (fun _ : Fin (dimN Ψ N j) => linLine Ψ N (muForm Ψ N j)) (vandLine Ψ N j) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [jForms]
  · simp [jForms, vandLine]

end Forms

end GlobalTheory.CompanionTheory.Ar.Giv.Push

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Push

theorem flagGrassPush : GlobalTheory.CompanionTheory.Ar.PB.Inputs → ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement →
    GroundTheory.Heights₂.Heights.LowerBoundFree.FlagGrassPush.Statement := by
  intro hIn hSys II Ψ _ _ _ N j cf hII hN hj hjN
  have hcnt : dimN Ψ N j + vandCount Ψ N j = dimFl Ψ N := VandCount.proof Ψ N j (by omega)
  have hAr0 : IsArithVar (PFl Ψ N) (dimFl Ψ N + 1) := FlagArithVar.proof Ψ N hN
  have hArFl : IsArithVar (PFl Ψ N) (dimN Ψ N j + 1 + vandCount Ψ N j) := by
    rwa [show dimFl Ψ N + 1 = dimN Ψ N j + 1 + vandCount Ψ N j by omega] at hAr0
  have hArFl' : IsArithVar (PFl Ψ N) (dimN Ψ N j + vandCount Ψ N j + 1) := by
    rwa [show dimN Ψ N j + 1 + vandCount Ψ N j = dimN Ψ N j + vandCount Ψ N j + 1 by omega] at hArFl
  have hArGr : IsArithVar (grassIdeal (Fintype.card Ψ) j (N - j)) (dimN Ψ N j + 1) :=
    GrassArithVar.full (Fintype.card Ψ) j (N - j) Fintype.card_pos
  have hIm := FlagImageGrass.proof Ψ N j hj hjN
  have hArIm : IsArithVar (imageZ (grFlV Ψ N j hj hjN) (PFl Ψ N)) (dimN Ψ N j + 1) := by
    rw [hIm]
    exact hArGr
  have hb := isBlockMap_grFl (Ψ := Ψ) (N := N) (j := j) hj hjN
  obtain ⟨G⟩ := Targets.genFibreExists _ _ _ _ _ _ (PFl Ψ N) _ hb hArFl
  obtain ⟨J, hJ, -⟩ := Targets.ExistsUnique.full G.Φ (fibreIdx (FlIdx Ψ N) (grFlKappa Ψ N j hj hjN))

  have hPF := hIn.projFormula II hII (Fin (Fintype.card Ψ)) (plBlocks (Fintype.card Ψ) j (N - j))
    (FlBlock Ψ N) (FlIdx Ψ N) (grFlKappa Ψ N j hj hjN) (grFlV Ψ N j hj hjN) (PFl Ψ N) (dimN Ψ N j + 1)
    (vandCount Ψ N j) G J (fun _ => fsHerm (plBlocks (Fintype.card Ψ) j (N - j)) (fun _ => -1))
    (fun _ => linLine Ψ N (muForm Ψ N j)) (vandLine Ψ N j) hb hArFl hArIm hJ
    (fun _ => isSmoothHerm_fsHerm _) (fun _ => isPullHerm_mu hj hjN) (fun _ => isSmoothHerm_fsHerm _)
  rw [hIm] at hPF
  have hprod := HFlProdLinear.proof FlagArithVar.proof II Ψ N (dimN Ψ N j + 1 + vandCount Ψ N j) cf
    (faForms Ψ N j) hII hN (by omega)
  rw [linLine_faForms Ψ N j, hPF, ← FA_eq_prod] at hprod
  have hinv := FsInvPow.proof II (Fin (Fintype.card Ψ)) (plBlocks (Fintype.card Ψ) j (N - j))
    (grassIdeal (Fintype.card Ψ) j (N - j)) (dimN Ψ N j + 1) hII hArGr

  have hgeo := ptsIntegral_projection hIn.projFormula ⟨II, hII⟩ (Fin (Fintype.card Ψ))
    (plBlocks (Fintype.card Ψ) j (N - j)) (FlBlock Ψ N) (FlIdx Ψ N) (grFlKappa Ψ N j hj hjN)
    (grFlV Ψ N j hj hjN) (PFl Ψ N) (dimN Ψ N j) (vandCount Ψ N j) G J
    (fun _ => fsHerm (plBlocks (Fintype.card Ψ) j (N - j)) (fun _ => -1))
    (fun _ => linLine Ψ N (muForm Ψ N j)) (vandLine Ψ N j) hb hArFl' hArIm hJ
    (fun _ => isSmoothHerm_fsHerm _) (fun _ => isPullHerm_mu hj hjN) (fun _ => isSmoothHerm_fsHerm _)
  rw [hIm, pts_neg_eq (hII _ _) hArGr, ← linLine_jForms,
    pts_linForms Ψ N II hII hN (fun w => GlobalTheory.T.flag_points_integral_product_formula hIn hSys Ψ N w hN) _ hcnt, prod_jForms] at hgeo
  have hJint : (Jint Ψ N j cf : ℝ) =
      (cf : ℝ) * ((flagInt Ψ N (muPoly Ψ N j ^ dimN Ψ N j * vandBlocks Ψ N j) : ℚ) : ℝ) := by
    unfold Jint fib
    rw [show muPoly Ψ N j ^ dimN Ψ N j * (C cf * vandBlocks Ψ N j) =
      C cf * (muPoly Ψ N j ^ dimN Ψ N j * vandBlocks Ψ N j) by ring, flagInt_C_mul]
    push_cast
    rfl
  rw [hprod, hinv, hJint, hgeo]
  ring

end GlobalTheory.CompanionTheory.Ar.Giv
end
end
end
