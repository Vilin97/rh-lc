module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagDualBasisSelfDualLatticeAtPlaceStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralTraceIdempotentAtTamePlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitarySupportedAtPlaceOfDualIsotropicFramStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceComapUnitarySupported
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceSplitsHyperbolicPlusCore
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeHyperbolicLineIdealsAtPlace
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralTraceIdempotentAtTamePlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

theorem _root_.GlobalTheory.T.exists_integral_trace_idempotent_at_tamePlace : ∀ (D : D7) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a), Tame D v → ∃ w ∈ intAt D (· = v), w + cA D w = ε := by
  first | exact @GlobalTheory.IwaPlace.exists_trace_one_at_tame | exact GlobalTheory.IwaPlace.exists_trace_one_at_tame | (intros; apply GlobalTheory.IwaPlace.exists_trace_one_at_tame <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsotropicDualColumnsSelfDualLatticeAtPlace

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open scoped TensorProduct

namespace GlobalTheory.IwaPlace.DualIso

variable {D : D7}

theorem intAE_mul_mem' {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem intAt_mul_mem {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [map_mul]; exact intAE_mul_mem' ha.2 hb.2⟩

theorem hermAt_smul_left (S : HSp D) (o : AE D) (y x : Fin S.rank → AE D) :
    hermAt S (o • y) x = o * hermAt S y x := by
  simp only [hermAt, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem smul_mem_of_isSDAt {S : HSp D} {v : Pl D} {M : AddSubgroup (Fin S.rank → AE D)} (hM : IsSDAt S v M)
    {o : AE D} (ho : o ∈ intAt D (· = v)) {y : Fin S.rank → AE D} (hy : y ∈ M) : o • y ∈ M := by
  refine (hM.2.2 _ fun i => ?_).2 fun x hx => ?_
  · simp only [Pi.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_left _ _ (hM.1 y hy i)
  · rw [hermAt_smul_left]; exact intAt_mul_mem ho ((hM.2.2 y (hM.1 y hy)).1 hy x hx)

theorem col_mul_mem {S : HSp D} {v : Pl D} {M : AddSubgroup (Fin S.rank → AE D)} (hM : IsSDAt S v M) {ρ : ℕ}
    (A : Mx D S.rank ρ) (B : Mx D ρ ρ) (hA : ∀ i, (fun k => A k i) ∈ M) (hB : ∀ m i, B m i ∈ intAt D (· = v))
    (i : Fin ρ) : (fun k => (A ⬝ B) k i) ∈ M := by
  have e : (fun k => (A ⬝ B) k i) = ∑ m, B m i • (fun k => A k m) := by
    funext k; simp [Matrix.mul_apply, Finset.sum_apply, mul_comm]
  rw [e]; exact AddSubgroup.sum_mem _ fun m _ => smul_mem_of_isSDAt hM (hB m i) (hA m)

theorem gram_entry (S : HSp D) {ρ : ℕ} (c' : Mx D S.rank ρ) (i j : Fin ρ) :
    (adj c' ⬝ (gA S ⬝ c')) i j = hermAt S (fun k => c' k j) (fun k => c' k i) := by
  simp only [hermAt, adj, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, mul_assoc]

theorem smul_mul_smul_one {ρ : ℕ} (ε w : AE D) (H : Mx D ρ ρ) : (ε • (1 : Mx D ρ ρ)) ⬝ (w • H) = (ε * w) • H := by
  rw [smul_mul_assoc, one_mul, smul_smul]

theorem smul_mul_smul_one' {ρ : ℕ} (ε w : AE D) (H : Mx D ρ ρ) : (w • H) ⬝ (ε • (1 : Mx D ρ ρ)) = (ε * w) • H := by
  rw [mul_smul_comm, mul_one, smul_smul]

theorem adj_gram_self (S : HSp D) {ρ : ℕ} (c' : Mx D S.rank ρ) : adj (adj c' ⬝ (gA S ⬝ c')) = adj c' ⬝ (gA S ⬝ c') := by
  rw [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

theorem gram_swap_smul (S : HSp D) {ρ : ℕ} {ε : AE D} (hεc : cA D ε = ε) (c c' : Mx D S.rank ρ)
    (hcc : adj c' ⬝ (gA S ⬝ c) = ε • (1 : Mx D ρ ρ)) : adj c ⬝ (gA S ⬝ c') = ε • (1 : Mx D ρ ρ) := by
  have := congrArg adj hcc
  rwa [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc, adj_smul, hεc, adj_one] at this

theorem pair_sub (S : HSp D) {ρ : ℕ} {ε : AE D} (c c' : Mx D S.rank ρ) (K : Mx D ρ ρ)
    (hcc0 : adj c ⬝ (gA S ⬝ c) = 0) (hcc : adj c' ⬝ (gA S ⬝ c) = ε • (1 : Mx D ρ ρ)) :
    adj (c' - c ⬝ K) ⬝ (gA S ⬝ c) = ε • (1 : Mx D ρ ρ) := by
  rw [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, hcc0, Matrix.mul_zero, sub_zero, hcc]

theorem pair_sub' (S : HSp D) {ρ : ℕ} {ε : AE D} (c c' : Mx D S.rank ρ) (K : Mx D ρ ρ)
    (hcc' : adj c ⬝ (gA S ⬝ c') = ε • (1 : Mx D ρ ρ)) :
    adj (c' - c ⬝ K) ⬝ (gA S ⬝ c') = adj c' ⬝ (gA S ⬝ c') - adj K ⬝ (ε • (1 : Mx D ρ ρ)) := by
  rw [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, hcc']

theorem self_sub (S : HSp D) {ρ : ℕ} (c'' c c' : Mx D S.rank ρ) (K : Mx D ρ ρ) (h : c'' = c' - c ⬝ K) :
    adj c'' ⬝ (gA S ⬝ c'') = adj c'' ⬝ (gA S ⬝ c') - adj c'' ⬝ (gA S ⬝ c) ⬝ K := by
  rw [h, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc (gA S) c K,
    ← Matrix.mul_assoc (adj (c' - c ⬝ K)) (gA S ⬝ c) K]

theorem isotropic_core {S : HSp D} {v : Pl D} {ε : AE D} (hεε : ε * ε = ε) (hεc : cA D ε = ε)
    (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) {M : AddSubgroup (Fin S.rank → AE D)} (hM : IsSDAt S v M)
    {w : AE D} (hw : w ∈ intAt D (· = v)) (hwc : w + cA D w = ε) {ρ : ℕ} (c c' : Mx D S.rank ρ)
    (hc : ∀ i, (fun k => c k i) ∈ M) (hc' : ∀ i, (fun k => c' k i) ∈ M) (hcc0 : adj c ⬝ (gA S ⬝ c) = 0)
    (hcc : adj c' ⬝ (gA S ⬝ c) = ε • (1 : Mx D ρ ρ)) :
    ∃ c'' : Mx D S.rank ρ, (∀ i, (fun k => c'' k i) ∈ M) ∧ adj c'' ⬝ (gA S ⬝ c) = ε • (1 : Mx D ρ ρ) ∧
      adj c'' ⬝ (gA S ⬝ c'') = 0 := by
  obtain ⟨H, hH⟩ : ∃ H : Mx D ρ ρ, H = adj c' ⬝ (gA S ⬝ c') := ⟨_, rfl⟩
  have hHint : ∀ i j, H i j ∈ intAt D (· = v) := fun i j => by
    rw [hH, gram_entry]; exact (hM.2.2 _ (hM.1 _ (hc' j))).1 (hc' j) _ (hc' i)
  have hεH : ε • H = H := by
    funext i j; rw [Matrix.smul_apply, smul_eq_mul]; exact (hε _).1 (hHint i j).1
  have hadjH : adj H = H := by rw [hH]; exact adj_gram_self S c'
  have hcc' := gram_swap_smul S hεc c c' hcc
  have hKint : ∀ m i, (w • H) m i ∈ intAt D (· = v) := fun m i => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact intAt_mul_mem hw (hHint m i)
  have e3 : ε * cA D w + ε * w = ε := by rw [← mul_add, add_comm, hwc, hεε]
  have f3 : H - (ε * cA D w) • H - (ε * w) • H = 0 := by
    rw [sub_sub, ← add_smul, e3, hεH, sub_self]
  have e1 := pair_sub S (ε := ε) c c' (w • H) hcc0 hcc
  have e2 := pair_sub' S c c' (w • H) hcc'
  rw [← hH, adj_smul, hadjH, smul_mul_smul_one'] at e2
  refine ⟨c' - c ⬝ (w • H), fun i => ?_, e1, ?_⟩
  · have e : (fun k => (c' - c ⬝ (w • H)) k i) = (fun k => c' k i) - fun k => (c ⬝ (w • H)) k i := rfl
    rw [e]; exact sub_mem (hc' i) (col_mul_mem hM c _ hc hKint i)
  · rw [self_sub S _ c c' (w • H) rfl, e1, e2, smul_mul_smul_one, f3]
theorem dual_isotropic : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (M : AddSubgroup (Fin S.rank → AE D)), IsSDAt S v M → ∀ w ∈ intAt D (· = v), w + cA D w = ε → ∀ (b : Mx D ρ ρ) (c' : Mx D S.rank ρ), (∀ i j, b i j ∈ idAt D (· = v)) → (∀ i, (fun k => (d.jX ⬝ b) k i) ∈ M) → (∀ i, (fun k => c' k i) ∈ M) → adj c' ⬝ (gA S ⬝ (d.jX ⬝ b)) = ε • (1 : Mx D ρ ρ) → ∃ c'' : Mx D S.rank ρ, (∀ i, (fun k => c'' k i) ∈ M) ∧ adj c'' ⬝ (gA S ⬝ (d.jX ⬝ b)) = ε • (1 : Mx D ρ ρ) ∧ adj c'' ⬝ (gA S ⬝ c'') = 0 := by
  intro D S S₀ ρ d v ε hεε hεc hεI hε M hM w hw hwc b c' hb hc hc' hcc
  have hcc0 : adj (d.jX ⬝ b) ⬝ (gA S ⬝ (d.jX ⬝ b)) = 0 := by
    rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) d.jX b, ← Matrix.mul_assoc (adj d.jX),
      d.gram_XX, Matrix.zero_mul, Matrix.mul_zero]
  exact isotropic_core hεε hεc hε hM hw hwc (d.jX ⬝ b) c' hc hc' hcc0 hcc

end GlobalTheory.IwaPlace.DualIso

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsotropicDualColumnsSelfDualLatticeAtPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

theorem _root_.GlobalTheory.T.exists_isotropic_dual_columns_selfDualLatticeAtPlace : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (M : AddSubgroup (Fin S.rank → AE D)), IsSDAt S v M → ∀ w ∈ intAt D (· = v), w + cA D w = ε → ∀ (b : Mx D ρ ρ) (c' : Mx D S.rank ρ), (∀ i j, b i j ∈ idAt D (· = v)) → (∀ i, (fun k => (d.jX * b) k i) ∈ M) → (∀ i, (fun k => c' k i) ∈ M) → adj c' * (gA S * (d.jX * b)) = ε • (1 : Mx D ρ ρ) → ∃ c'' : Mx D S.rank ρ, (∀ i, (fun k => c'' k i) ∈ M) ∧ adj c'' * (gA S * (d.jX * b)) = ε • (1 : Mx D ρ ρ) ∧ adj c'' * (gA S * c'') = 0 := by
  intro D S S₀ ρ d v ε hεε hεc hεI hε M hM w hw hwc b c' hb hc hc' hcc
  let c : Mx D S.rank ρ := d.jX * b
  change adj c' * (gA S * c) = ε • (1 : Mx D ρ ρ) at hcc
  have hcc0 : adj c * (gA S * c) = 0 := by
    dsimp only [c]
    rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) d.jX b,
      ← Matrix.mul_assoc (adj d.jX), d.gram_XX, Matrix.zero_mul, Matrix.mul_zero]
  have hcc' : adj c * (gA S * c') = ε • (1 : Mx D ρ ρ) := by
    have h := congrArg adj hcc
    rwa [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc, adj_smul, hεc, adj_one] at h
  let H : Mx D ρ ρ := adj c' * (gA S * c')
  have hHint (i j : Fin ρ) : H i j ∈ intAt D (· = v) := by
    have hgram : H i j = hermAt S (fun k => c' k j) (fun k => c' k i) := by
      simp only [H, hermAt, adj, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
        Finset.mul_sum, mul_assoc]
    rw [hgram]
    exact (hM.2.2 _ (hM.1 _ (hc' j))).1 (hc' j) _ (hc' i)
  have hεH : ε • H = H := by
    funext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (hε _).1 (hHint i j).1
  have hadjH : adj H = H := by
    dsimp only [H]
    rw [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]
  let K : Mx D ρ ρ := w • H
  have hKint (m i : Fin ρ) : K m i ∈ intAt D (· = v) := by
    change (w • H) m i ∈ intAt D (· = v)
    rw [Matrix.smul_apply, smul_eq_mul]
    exact GlobalTheory.IwaPlace.DualIso.intAt_mul_mem hw (hHint m i)
  let c'' : Mx D S.rank ρ := c' - c * K
  have hpair : adj c'' * (gA S * c) = ε • (1 : Mx D ρ ρ) := by
    dsimp only [c'']
    rw [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, hcc0, Matrix.mul_zero,
      sub_zero, hcc]
  refine ⟨c'', ?_, hpair, ?_⟩
  · intro i
    have hcol : (fun k => (c * K) k i) = ∑ m, K m i • (fun k => c k m) := by
      funext k
      simp [Matrix.mul_apply, Finset.sum_apply, mul_comm]
    change (fun k => c' k i) - (fun k => (c * K) k i) ∈ M
    rw [hcol]
    exact sub_mem (hc' i) (AddSubgroup.sum_mem _ fun m _ =>
      GlobalTheory.IwaPlace.DualIso.smul_mem_of_isSDAt hM (hKint m i) (hc m))
  · have hleft : adj c'' * (gA S * c') = H - (ε * cA D w) • H := by
      dsimp only [c'']
      rw [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, hcc']
      change H - adj (w • H) * (ε • (1 : Mx D ρ ρ)) = _
      rw [adj_smul, hadjH, mul_smul_comm, mul_one, smul_smul]
    have hsum : ε * cA D w + ε * w = ε := by
      rw [← mul_add, add_comm, hwc, hεε]
    calc
      adj c'' * (gA S * c'') =
          adj c'' * (gA S * c') - (adj c'' * (gA S * c)) * K := by
        change adj c'' * (gA S * (c' - c * K)) = _
        rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc (gA S) c K,
          ← Matrix.mul_assoc (adj c'') (gA S * c) K]
      _ = H - (ε * cA D w) • H - (ε * w) • H := by
        rw [hleft, hpair]
        change H - (ε * cA D w) • H - (ε • (1 : Mx D ρ ρ)) * (w • H) = _
        rw [smul_mul_assoc, one_mul, smul_smul]
      _ = 0 := by rw [sub_sub, ← add_smul, hsum, hεH, sub_self]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceComapUnitarySupportedStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

theorem _root_.GlobalTheory.T.isSelfDualLatticeAtPlace_comap_unitarySupported : ∀ (D : D7) (S : HSp D) (v : Pl D) (g : GA D S), g ∈ grpAt S (· = v) → ∀ Λ : AddSubgroup (Fin S.rank → AE D), IsSDAt S v Λ → IsSDAt S v (Λ.comap (Matrix.mulVecLin (mt S g)).toAddMonoidHom) := by
  first | exact @GlobalTheory.IwaPlace.SdComap.isSDAt_comap | exact GlobalTheory.IwaPlace.SdComap.isSDAt_comap | (intros; apply GlobalTheory.IwaPlace.SdComap.isSDAt_comap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceSplitsHyperbolicPlusCoreStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

theorem _root_.GlobalTheory.T.selfDualLatticeAtPlace_splits_hyperbolic_plus_core : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (N : AddSubgroup (Fin S.rank → AE D)) (α β : Fin ρ → AE D), IsSDAt S v N → (∀ i, α i ∈ idAt D (· = v)) → (∀ i, β i ∈ idAt D (· = v)) → (∀ i, α i * β i = ε) → (∀ i, colMul d.jX i (α i) ∈ N) → (∀ i, colMul d.jY i (cA D (β i)) ∈ N) → ∃ Λ₀ : AddSubgroup (Fin S₀.rank → AE D), IsSDAt S₀ v Λ₀ ∧ ∀ z : Fin S.rank → AE D, (∀ i, z i ∈ idAt D (· = v)) → (z ∈ N ↔ (∀ i, (d.pX *ᵥ z) i * β i ∈ intAt D (· = v)) ∧ (∀ i, (d.pY *ᵥ z) i * cA D (α i) ∈ intAt D (· = v)) ∧ d.p0 *ᵥ z ∈ Λ₀) := by
  first | exact @GlobalTheory.IwaDecomp.selfDual_split | exact GlobalTheory.IwaDecomp.selfDual_split | (intros; apply GlobalTheory.IwaDecomp.selfDual_split <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeHyperbolicLineIdealsAtPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

theorem _root_.GlobalTheory.T.selfDualLattice_hyperbolic_line_ideals_at_place : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a), IsSDAt S v (latV S L (· = v)) → MonoAt d L L₀ v → ∃ α β : Fin ρ → AE D, (∀ i, α i ∈ idAt D (· = v)) ∧ (∀ i, β i ∈ idAt D (· = v)) ∧ (∀ i, α i * β i = ε) ∧ (∀ i, ∀ a ∈ idAt D (· = v), colMul d.jX i a ∈ latV S L (· = v) ↔ a * β i ∈ intAt D (· = v)) ∧ (∀ i, ∀ a ∈ idAt D (· = v), colMul d.jY i a ∈ latV S L (· = v) ↔ a * cA D (α i) ∈ intAt D (· = v)) := by
  first | exact @GlobalTheory.IwaIdeals.ideals_at_place | exact GlobalTheory.IwaIdeals.ideals_at_place | (intros; apply GlobalTheory.IwaIdeals.ideals_at_place <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagStabiliserMoveLatticeSplitWitt

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

noncomputable section

namespace GlobalTheory.IwaPlace

theorem iwasawa_flag_move : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), Tame D v → IsSDAt S v (latV S L (· = v)) → MonoAt d L L₀ v → ∀ h ∈ grpAt S (· = v), ∃ q ∈ grpAt S (· = v), (∃ a : Mx D ρ ρ, (∀ i j, j < i → a i j = 0) ∧ mt S q ⬝ d.jX = d.jX ⬝ a) ∧ ∃ Λ₀ : AddSubgroup (Fin S₀.rank → AE D), IsSDAt S₀ v Λ₀ ∧ ∀ z : Fin S.rank → AE D, (∀ i, z i ∈ idAt D (· = v)) → (mt S (h⁻¹ * q) *ᵥ z ∈ latV S L (· = v) ↔ (∀ i, colMul d.jX i ((d.pX *ᵥ z) i) ∈ latV S L (· = v)) ∧ (∀ i, colMul d.jY i ((d.pY *ᵥ z) i) ∈ latV S L (· = v)) ∧ d.p0 *ᵥ z ∈ Λ₀) := by
  intro D S S₀ ρ d L L₀ v hT hL hM h hh
  obtain ⟨⟨ε, hεε, hεc, hεI, hε, -⟩, -⟩ := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)
  have hMsd := GlobalTheory.T.isSelfDualLatticeAtPlace_comap_unitarySupported D S v h⁻¹ (inv_mem hh) _ hL
  set M := (latV S L (· = v)).comap (Matrix.mulVecLin (mt S h⁻¹)).toAddMonoidHom with hMdef
  obtain ⟨b, hbu, hbI, hbM, c', hc'M, hpair⟩ := GlobalTheory.T.exists_flag_dual_basis_selfDualLatticeAtPlace D S S₀ ρ d v ε hεε hεc hεI hε hT M hMsd
  obtain ⟨w, hw, hw1⟩ := GlobalTheory.T.exists_integral_trace_idempotent_at_tamePlace D v ε hεε hεc hεI hε hT
  obtain ⟨c'', hc''M, hpair', hiso⟩ := GlobalTheory.T.exists_isotropic_dual_columns_selfDualLatticeAtPlace D S S₀ ρ d v ε hεε hεc hεI hε M hMsd w hw hw1 b c' hbI hbM hc'M hpair
  obtain ⟨α, β, hα, hβ, hαβ, hX, hY⟩ := GlobalTheory.T.selfDualLattice_hyperbolic_line_ideals_at_place D S S₀ ρ d L L₀ v ε hεε hεc hεI hε hL hM
  have hc''I : ∀ i j, c'' i j ∈ idAt D (· = v) := fun i j => hMsd.1 _ (hc''M j) i
  obtain ⟨q, hq, hqX, hqα, hqβ⟩ := GlobalTheory.T.exists_unitarySupportedAtPlace_of_dual_isotropic_frames D S S₀ ρ d v ε hεε hεc hεI hε α β b c'' hα hβ hαβ hbI hc''I hpair' hiso
  have hNsd := GlobalTheory.T.isSelfDualLatticeAtPlace_comap_unitarySupported D S v q hq M hMsd
  obtain ⟨Λ₀, hΛ, hz⟩ := GlobalTheory.T.selfDualLatticeAtPlace_splits_hyperbolic_plus_core D S S₀ ρ d v ε hεε hεc hεI hε _ α β hNsd hα hβ hαβ
    (fun i => by
      rw [AddSubgroup.mem_comap]
      change mt S q *ᵥ colMul d.jX i (α i) ∈ M
      rw [hqα]; exact hbM i)
    (fun i => by
      rw [AddSubgroup.mem_comap]
      change mt S q *ᵥ colMul d.jY i (cA D (β i)) ∈ M
      rw [hqβ]; exact hc''M i)
  refine ⟨q, hq, ⟨b ⬝ Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ), fun i j hji => ?_, hqX⟩, Λ₀, hΛ, fun z hz' => ?_⟩
  · rw [Matrix.add_apply, Matrix.mul_diagonal, hbu i j hji, Matrix.smul_apply, Matrix.one_apply_ne (ne_of_gt hji)]
    simp
  · have e1 : (mt S (h⁻¹ * q) *ᵥ z ∈ latV S L (· = v)) ↔
        z ∈ (M.comap (Matrix.mulVecLin (mt S q)).toAddMonoidHom) := by
      rw [AddSubgroup.mem_comap, hMdef, AddSubgroup.mem_comap]
      change _ ↔ mt S h⁻¹ *ᵥ (mt S q *ᵥ z) ∈ _
      rw [Matrix.mulVec_mulVec, ← mt_mul]
    rw [e1, hz z hz']
    refine and_congr (forall_congr' fun i => (hX i _ (mulVec_mem_idAt _ hz' i)).symm)
      (and_congr (forall_congr' fun i => (hY i _ (mulVec_mem_idAt _ hz' i)).symm) Iff.rfl)

end GlobalTheory.IwaPlace

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagStabiliserMoveLatticeSplitWittStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

theorem _root_.GlobalTheory.T.exists_flag_stabiliser_move_lattice_split_witt : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), Tame D v → IsSDAt S v (latV S L (· = v)) → MonoAt d L L₀ v → ∀ h ∈ grpAt S (· = v), ∃ q ∈ grpAt S (· = v), (∃ a : Mx D ρ ρ, (∀ i j, j < i → a i j = 0) ∧ mt S q ⬝ d.jX = d.jX ⬝ a) ∧ ∃ Λ₀ : AddSubgroup (Fin S₀.rank → AE D), IsSDAt S₀ v Λ₀ ∧ ∀ z : Fin S.rank → AE D, (∀ i, z i ∈ idAt D (· = v)) → (mt S (h⁻¹ * q) *ᵥ z ∈ latV S L (· = v) ↔ (∀ i, colMul d.jX i ((d.pX *ᵥ z) i) ∈ latV S L (· = v)) ∧ (∀ i, colMul d.jY i ((d.pY *ᵥ z) i) ∈ latV S L (· = v)) ∧ d.p0 *ᵥ z ∈ Λ₀) := by
  first | exact @GlobalTheory.IwaPlace.iwasawa_flag_move | exact GlobalTheory.IwaPlace.iwasawa_flag_move | (intros; apply GlobalTheory.IwaPlace.iwasawa_flag_move <;> assumption)
end
end
