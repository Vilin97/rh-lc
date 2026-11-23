module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiExteriorTensorSmoothIrreducibleIsIrreducibleStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalCellMultiplicityOfColouringStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalMultiplicityProductZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedProductDropZeroFactorsStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepJacquetWordMultiplicityStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.BitVec

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalMultiplicityProductZeroStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.cuspidal_multiplicity_product_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ (ρ : IrrGL (k := k)) {h : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = ρ.1), ρ.IsCusp → 2 ≤ h → (∀ a, 0 < (x a).1) → jhMult ρ.rep (prodIrr x hd) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CuspNotInd.jhMult_eq_zero_of_isCusp | exact GlobalTheory.CompanionTheory.CuspNotInd.jhMult_eq_zero_of_isCusp | (intros; apply GlobalTheory.CompanionTheory.CuspNotInd.jhMult_eq_zero_of_isCusp <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalCellMultiplicityZeroOfSplitColumn

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

noncomputable section

namespace GlobalTheory.CompanionTheory.FineProd.CellMulti



theorem jhMult_cell_eq_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {h r : ℕ} (x : Fin h → IrrGL (k := k)) (y : Fin r → IrrGL (k := k)), (∀ j, (y j).IsCusp) → ∀ (b : Fin h → Fin r → ℕ) (hrow : ∀ i, ∑ j, b i j = (x i).1) (hcol : ∀ j, ∑ i, b i j = (y j).1) (j : Fin r) (i i' : Fin h), i ≠ i' → b i j ≠ 0 → b i' j ≠ 0 → jhMult (piTensor fun j => (y j).rep) (cellFunctor (c := fun i j => Fin (b i j)) (fun i => stdBlocks (b i) (hrow i)) (fun j => stdBlocks (fun i => b i j) (hcol j)) (piTensor fun i => (x i).rep)) = 0 := by
  intro k _ _ _ _ hA h r x y hy b hrow hcol j i i' hii hi hi'
  classical
  by_contra h0
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hτ : (piTensor fun j => (y j).rep).IsIrreducible := GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => (y j).2.rep
  have hτs : IsSmooth (piTensor fun j => (y j).rep) := isSmooth_piTensor fun j => (y j).2.rep.smooth
  obtain ⟨s, -, hS⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_of_cell (GlobalTheory.CompanionTheory.GeoLink.geometricLemma k).2 _ _
    (fun i => (x i).2.rep.smooth) (fun i => hasFiniteLength_of_isIrreducible (x i).2.rep.irr) hτ hτs h0
  have h1 := GlobalTheory.LocGL.SupportUnique.isSubquotient_factor (fun j => multiProd (stdBlocks (fun i => b i j) (hcol j)) fun i => (s i j).ρ) j
    (y j).2.rep.irr
    ((GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun j => (y j).rep) (fun j => (y j).2.rep.irr) j).trans
      (GlobalTheory.LocGL.SupportUnique.isSubquotient_comp hS _))
  let Y : Fin h → IrrGL (k := k) := fun i => IrrGL.of (s i j).ρ (s i j).smooth (s i j).irr
  have hYb : ∀ c, (Y c).1 = b c j := fun _ => rfl
  let ψ := prodIrrEquiv (hcol j) (fun i => (s i j).ρ) (fun i => (s i j).smooth) fun i => (s i j).irr
  have h2 := h1.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective)
  let S : Finset (Fin h) := Finset.univ.filter fun c => b c j ≠ 0
  let o : Fin S.card ↪o Fin h := S.orderEmbOfFin rfl
  have hcard : 2 ≤ S.card := Finset.one_lt_card.2 ⟨i, by simp [S, hi], i', by simp [S, hi'], hii⟩
  have ho : ∀ a, o a ∈ S := fun a => Finset.orderEmbOfFin_mem _ _ _
  have hrange : ∀ c, (Y c).1 ≠ 0 → c ∈ Set.range o := fun c hc => by
    rw [Finset.range_orderEmbOfFin]
    simpa [S, hYb] using hc
  have hsum : ∑ a, (Y (o a)).1 = (y j).1 := by
    have e1 : ∑ a, (Y (o a)).1 = ∑ c : S, b c j :=
      Fintype.sum_equiv (S.orderIsoOfFin rfl).toEquiv _ _ fun a => rfl
    rw [e1, Finset.sum_coe_sort S (fun c => b c j), ← hcol j]
    exact Finset.sum_subset (Finset.subset_univ _) fun c _ hc => by simpa [S] using hc
  obtain ⟨E⟩ := GlobalTheory.T.induced_product_drop_zero_factors Y (hcol j) o o.strictMono hrange hsum
  have h3 := h2.trans (.of_injective E.toIntertwiningMap E.toLinearEquiv.injective)
  refine jhMult_ne_zero_iff.2 h3
    (GlobalTheory.T.cuspidal_multiplicity_product_zero hA (y j) (fun a => Y (o a)) hsum (hy j) hcard fun a => Nat.pos_of_ne_zero ?_)
  have := ho a
  simpa [S, hYb] using this

end GlobalTheory.CompanionTheory.FineProd.CellMulti
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalCellMultiplicityZeroOfSplitColumnStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.cuspidal_cell_multiplicity_zero_of_split_column : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {h r : ℕ} (x : Fin h → IrrGL (k := k)) (y : Fin r → IrrGL (k := k)), (∀ j, (y j).IsCusp) → ∀ (b : Fin h → Fin r → ℕ) (hrow : ∀ i, ∑ j, b i j = (x i).1) (hcol : ∀ j, ∑ i, b i j = (y j).1) (j : Fin r) (i i' : Fin h), i ≠ i' → b i j ≠ 0 → b i' j ≠ 0 → jhMult (piTensor fun j => (y j).rep) (cellFunctor (c := fun i j => Fin (b i j)) (fun i => stdBlocks (b i) (hrow i)) (fun j => stdBlocks (fun i => b i j) (hcol j)) (piTensor fun i => (x i).rep)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.FineProd.CellMulti.jhMult_cell_eq_zero | exact GlobalTheory.CompanionTheory.FineProd.CellMulti.jhMult_cell_eq_zero | (intros; apply GlobalTheory.CompanionTheory.FineProd.CellMulti.jhMult_cell_eq_zero <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductJacquetShuffleCount

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineProd

theorem sum_map_filter {β : Type*} (p : β → Prop) [DecidablePred p] (f : β → ℕ) (l : List β) :
    ((l.filter fun a => decide (p a)).map f).sum = (l.map fun j => if p j then f j else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hp : p a
    · simp [List.filter_cons, hp, ih]
    · simp [List.filter_cons, hp, ih]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem deg_sub {h : ℕ} (W : List (IrrGL (k := k))) (c : Fin W.length → Fin h) (i : Fin h) :
    ((sub W c i).map Sigma.fst).sum = ∑ j, if c j = i then (W.get j).1 else 0 := by
  show ((List.map W.get (List.filter (fun p => decide (c p = i)) (List.finRange W.length))).map
    Sigma.fst).sum = _
  rw [List.map_map, Fin.sum_univ_def]
  exact sum_map_filter (fun p => c p = i) (fun p => (W.get p).1) (List.finRange W.length)

theorem deg_decWord (Γ : Segment k) : ((decWord Γ).map Sigma.fst).sum = Γ.deg := by
  have h : ∀ a, (Γ.term a).1 = Γ.d := fun a => rfl
  show ((List.ofFn Γ.term).reverse.map Sigma.fst).sum = Γ.len * Γ.d
  rw [List.map_reverse, List.sum_reverse, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_def, h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

def colourMat {h : ℕ} (W : List (IrrGL (k := k))) (c : Fin W.length → Fin h) (i : Fin h) (j : Fin W.length) : ℕ :=
  if c j = i then (W.get j).1 else 0

theorem sum_colourMat {h : ℕ} (W : List (IrrGL (k := k))) (c : Fin W.length → Fin h) (j : Fin W.length) :
    ∑ i, colourMat W c i j = (W.get j).1 := by
  simp [colourMat]

end GlobalTheory.CompanionTheory.FineProd


open GlobalTheory.CompanionTheory.FineProd in
theorem GlobalTheory.CompanionTheory.FineProd.jmL_prodIrr : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), (∀ i, IsLSeg (Γ i) (x i).rep) → ∀ W : List (IrrGL (k := k)), (∀ w ∈ W, w.IsCusp) → jmL W (prodIrr x hd) = (shuffleCount W (fun i => decWord (Γ i)) : ℕ∞) := by
  intro k _ _ _ _ hA hJ h N Γ x hd hΓ W hW
  classical
  have hΓd : ∀ i, ((decWord (Γ i)).map Sigma.fst).sum = (x i).1 := fun i =>
    (deg_decWord _).trans (hΓ i).deg_eq
  let S : Finset (Fin W.length → Fin h) := Finset.univ.filter fun c => ∀ i, sub W c i = decWord (Γ i)
  have hcount : shuffleCount W (fun i => decWord (Γ i)) = S.card := by
    unfold shuffleCount
    congr
  have hrowS : ∀ c ∈ S, ∀ i, ∑ j, colourMat W c i j = (x i).1 := fun c hc i => by
    have h1 := (Finset.mem_filter.1 hc).2 i
    have h2 := deg_sub W c i
    rw [h1, hΓd] at h2
    exact h2.symm
  have hSdeg : ∀ c ∈ S, ∑ a, (W.get a).1 = N := fun c hc => by
    rw [← hd, ← Finset.sum_congr rfl fun i _ => hrowS c hc i, Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => (sum_colourMat W c j).symm
  have hpos : ∀ j, 0 < (W.get j).1 := fun j => (hW _ (List.get_mem _ _)).1
  rw [hcount]
  by_cases hWd : ∑ a, (W.get a).1 = N
  swap
  · have hSe : S = ∅ := Finset.eq_empty_of_forall_notMem fun c hc => hWd (hSdeg c hc)
    rw [hSe, jmL, dite_eq_right hWd]
    simp
  let m : Fin h → Type := fun i => Fin (x i).1
  let m' : Fin W.length → Type := fun j => Fin (W.get j).1
  haveI : Fintype (SizeMatrix m m') := Fintype.ofFinite _
  have hr : ∀ (b : SizeMatrix m m') i, ∑ j, b.1 i j = (x i).1 := fun b i => by
    simpa [m] using b.2.1 i
  have hc : ∀ (b : SizeMatrix m m') j, ∑ i, b.1 i j = (W.get j).1 := fun b j => by
    simpa [m'] using b.2.2 j
  have hτ : (piTensor fun j => (W.get j).rep).IsIrreducible :=
    GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k _ _ fun j => (W.get j).2.rep
  have key := ((GlobalTheory.CompanionTheory.GeoLink.geometricLemma k).1).jhMult_eq (m := m) (m' := m')
    (stdBlocks (fun a => (x a).1) hd) (stdBlocks (fun a => (W.get a).1) hWd)
    (isSmooth_piTensor fun i => (x i).2.rep.smooth)
    (fun b i => stdBlocks (b.1 i) (hr b i)) (fun b j => stdBlocks (fun i => b.1 i j) (hc b j)) hτ
  have hF : ∀ b : SizeMatrix m m', jhMult (piTensor fun j => (W.get j).rep)
      (cellFunctor (c := fun i j => Fin (b.1 i j)) (fun i => stdBlocks (b.1 i) (hr b i))
        (fun j => stdBlocks (fun i => b.1 i j) (hc b j)) (piTensor fun i => (x i).rep)) =
      if ∃ c ∈ S, b.1 = colourMat W c then 1 else 0 := by
    intro b
    split_ifs with hb
    · obtain ⟨c, hcS, hbc⟩ := hb
      rw [GlobalTheory.T.cuspidal_cell_multiplicity_of_colouring x W b.1 (hr b) (hc b) c (fun i j => by rw [hbc]; rfl)]
      refine Finset.prod_eq_one fun i _ => ?_
      refine ((GlobalTheory.T.segment_rep_jacquet_word_multiplicity hA hJ (Γ i) (x i).rep (hΓ i) (sub W c i) fun w hw => ?_).1
        ((Finset.mem_filter.1 hcS).2 i))
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hw
      exact hW _ (List.get_mem _ _)
    · by_cases hm : ∃ (j : Fin W.length) (i i' : Fin h), i ≠ i' ∧ b.1 i j ≠ 0 ∧ b.1 i' j ≠ 0
      · obtain ⟨j, i, i', hii, h1, h2⟩ := hm
        exact GlobalTheory.T.cuspidal_cell_multiplicity_zero_of_split_column hA x (fun j => W.get j) (fun j => hW _ (List.get_mem _ _)) b.1 (hr b) (hc b) j i i' hii h1 h2
      · push_neg at hm
        have hex : ∀ j, ∃ i, b.1 i j ≠ 0 := fun j => by
          by_contra hne
          push_neg at hne
          have := hc b j
          rw [Finset.sum_eq_zero fun i _ => hne i] at this
          exact (hpos j).ne this
        choose c hcj using hex
        have hzero : ∀ i j, c j ≠ i → b.1 i j = 0 := fun i j hij => by
          by_contra hne
          exact hne (hm j (c j) i hij (hcj j))
        have hbc : b.1 = colourMat W c := by
          funext i j
          unfold colourMat
          split_ifs with hij
          · subst hij
            rw [← hc b j]
            exact (Finset.sum_eq_single (c j) (fun i _ hi => hzero i j (Ne.symm hi)) (by simp)).symm
          · exact hzero i j hij
        have hcS : c ∉ S := fun hcS => hb ⟨c, hcS, hbc⟩
        have hex2 : ∃ i, sub W c i ≠ decWord (Γ i) := by
          by_contra hne
          push_neg at hne
          exact hcS (Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩)
        obtain ⟨i, hi⟩ := hex2
        rw [GlobalTheory.T.cuspidal_cell_multiplicity_of_colouring x W b.1 (hr b) (hc b) c (fun i j => by rw [hbc]; rfl)]
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        refine (GlobalTheory.T.segment_rep_jacquet_word_multiplicity hA hJ (Γ i) (x i).rep (hΓ i) (sub W c i) (fun w hw => ?_)).2 hi
        obtain ⟨p, -, rfl⟩ := List.mem_map.1 hw
        exact hW _ (List.get_mem _ _)
  rw [jmL, dite_eq_left hWd]
  refine Eq.trans key ?_
  have hcard : (Finset.univ.filter fun b : SizeMatrix m m' => ∃ c ∈ S, b.1 = colourMat W c).card = S.card := by
    symm
    let mk : ∀ c, c ∈ S → SizeMatrix m m' := fun c hc =>
      ⟨colourMat W c, fun i => by simpa [m] using hrowS c hc i, fun j => by simpa [m'] using sum_colourMat W c j⟩
    refine Finset.card_bij mk (fun c hc => Finset.mem_filter.2 ⟨Finset.mem_univ _, c, hc, rfl⟩) ?_ ?_
    · intro c hc c' hc' he
      funext j
      have h1 : colourMat W c (c j) j = colourMat W c' (c j) j :=
        congrFun (congrFun (congrArg Subtype.val he) (c j)) j
      by_contra hne
      have h2 : c' j ≠ c j := fun e => hne e.symm
      simp only [colourMat, if_true, if_neg h2] at h1
      exact (hpos j).ne' h1
    · intro b hb
      obtain ⟨c, hc, hbc⟩ := (Finset.mem_filter.1 hb).2
      exact ⟨c, hc, Subtype.ext hbc.symm⟩
  rw [Finset.sum_congr rfl fun b _ => hF b, Finset.sum_boole, hcard]
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductJacquetShuffleCountStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.segment_product_jacquet_shuffle_count : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), (∀ i, IsLSeg (Γ i) (x i).rep) → ∀ W : List (IrrGL (k := k)), (∀ w ∈ W, w.IsCusp) → jmL W (prodIrr x hd) = (shuffleCount W (fun i => decWord (Γ i)) : ℕ∞) := by
  first | exact @GlobalTheory.CompanionTheory.FineProd.jmL_prodIrr | exact GlobalTheory.CompanionTheory.FineProd.jmL_prodIrr | (intros; apply GlobalTheory.CompanionTheory.FineProd.jmL_prodIrr <;> assumption)
end
end
