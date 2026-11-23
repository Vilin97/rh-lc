module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PaddedLastEntry
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.MeanPeriodLogarithms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BadPrimesSharp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormMuInvDetZeroOrOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SharpUnitAtBadPrimesStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Formalism.LocalToGlobal.Columns.BaseLemmas
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetCConstMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConstantExponentsFiniteStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogMetricGeneratorEqMeanPeriodStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyStandardLatticesEqBaseVectorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumDatumNumbersEqHostOfCompatibleStatement
import Mathlib.Algebra.Order.Star.Int

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantNinth

section

@[expose] public section

namespace GlobalTheory.ColNorms.StepRows

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem nuW_eq_nu (N : NumDatum) {X : Fields} {Pr : Primes X} (W : Wts X Pr.Word N.R) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word)
    (δ : Code N) (h : WeightTie N W pl u δ) {i : ℕ} (hi : i < N.R.m) (z : RPl N.R) (l : Fin (N.R.N i)) :
    (((W.nuW u (i + 1) (pl z)).w l : ℤ) : ℚ) = N.nu δ (i + 1) z l := by
  obtain ⟨h1, h2⟩ := h.2.2 z
  have he : (W.hc u (pl z)).e = (N.hc z).e := congrArg RowPar.e h1
  have hq : N.eQ (i + 1) z = (N.hc z).e ⟨i, hi⟩ := by
    unfold NumDatum.eQ
    rw [dite_eq_left ⟨by omega, by omega⟩]
    rfl
  rw [W.nuW_eq u hi, W.lamN_eq u hi.le, he]
  unfold NumDatum.nu NumDatum.srcPar
  rw [hq]
  by_cases hl : l.1 < N.R.k
  · rw [dite_eq_left hl, dite_eq_left hl]
    unfold hcToWeightQ rhoVec wG Ranks.N
    rw [h2, Nat.add_sub_cancel]
    push_cast
    ring
  · have hb := N.R.blk_lt hi.le l hl
    rw [dite_eq_right hl, dite_eq_right hl, dite_eq_left hb]
    have hdm := Nat.div_add_mod (l.1 - N.R.k) (N.R.t + 1)
    have hl2 : l.1 = N.R.k + ((N.R.t + 1) * ((l.1 - N.R.k) / (N.R.t + 1)) + (l.1 - N.R.k) % (N.R.t + 1)) := by omega
    have hl3 : ((l.1 : ℕ) : ℚ) = N.R.k + (((N.R.t : ℚ) + 1) * (((l.1 - N.R.k) / (N.R.t + 1) : ℕ) : ℚ) +
        (((l.1 - N.R.k) % (N.R.t + 1) : ℕ) : ℚ)) := by exact_mod_cast hl2
    rw [hl3]
    generalize (N.hc z).e ⟨(l.1 - N.R.k) / (N.R.t + 1), hb⟩ = eb
    generalize (l.1 - N.R.k) / (N.R.t + 1) = B
    generalize (l.1 - N.R.k) % (N.R.t + 1) = r
    unfold wG Ranks.N
    rw [Nat.add_sub_cancel]
    push_cast
    ring

theorem sExp_int (R : Ranks) (z : ℤ) (j : ℕ) :
    (∃ y : ℤ, sExp R (z : ℚ) (j + 1) = y) ∧ ∃ y : ℤ, sExp' R (z : ℚ) (j + 1) = y := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨c, hc⟩ := R.t_odd
  unfold sExp sExp' Ranks.N
  rw [Nat.add_sub_cancel, ha, hc]
  exact ⟨⟨z - a - j * (c + 1), by push_cast; ring⟩, ⟨z - a - (j + 1) * (c + 1), by push_cast; ring⟩⟩

theorem stepWeights {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R) (u : Word) {i : ℕ} (hi : i < R.m) (τ : X.Tau)
    (h0 : ∀ l : Fin (R.N i), 0 ≤ (W.nuW u (i + 1) τ).w l) :
    GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.StepWeights (W.lamTrue u i τ) (W.nuW u (i + 1) τ) (W.lamTrue u (i + 1) τ) := by
  obtain ⟨z, hz⟩ := (W.hc u τ).e_int ⟨i, hi⟩
  obtain ⟨⟨y, hy⟩, ⟨y', hy'⟩⟩ := sExp_int R z i
  refine ⟨h0, ⟨y', fun l => ?_⟩, ⟨y, fun l => ?_⟩⟩
  · have h := W.nuW_eq_true u hi τ l
    rw [hz, hy'] at h
    exact_mod_cast h
  · unfold GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.padZero
    by_cases hl : l.1 < R.N i
    · rw [dite_eq_left hl]
      have h := W.nuW_eq_true u hi τ ⟨l.1, hl⟩
      have h' := W.lamTrue_old u hi τ l hl
      rw [hz, hy'] at h
      rw [hz, hy, hy', ← h] at h'
      have h2 : (((W.lamTrue u (i + 1) τ).w l + y : ℤ) : ℚ) = (((W.nuW u (i + 1) τ).w ⟨l.1, hl⟩ : ℤ) : ℚ) := by
        push_cast
        rw [h']
        ring
      exact_mod_cast h2
    · rw [dite_eq_right hl]
      have h' := W.lamTrue_new u hi τ l hl
      rw [hz, hy] at h'
      have h2 : (((W.lamTrue u (i + 1) τ).w l + y : ℤ) : ℚ) = 0 := by
        push_cast
        rw [h']
        ring
      exact_mod_cast h2

end GlobalTheory.ColNorms.StepRows
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeightsRows

section

@[expose] public section

namespace GlobalTheory.Core.Ht2.StepRowsS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

theorem weights_rows : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i < N.R.m → (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.StepWeights (W.lamTrue u i τ) (W.nuW u (i + 1) τ) (W.lamTrue u (i + 1) τ)) ∧ ∀ (z : RPl N.R) (l : Fin (N.R.N i)), (((W.nuW u (i + 1) (pl z)).w l : ℤ) : ℚ) = N.nu δ (i + 1) z l := by
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ hyp i hi
  obtain ⟨-, hW, -, -, -, -, -, -, hS⟩ := hyp
  refine ⟨fun τ => StepRows.stepWeights W u hi τ fun l => ?_, fun z l => StepRows.nuW_eq_nu N W pl u δ hW hi z l⟩
  obtain ⟨z, rfl⟩ := pl.surjective τ
  have h1 := StepRows.nuW_eq_nu N W pl u δ hW hi z l
  have h2 := (hS.2.2.2.2.1 (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩) z l.1 l.2).1
  rw [← h1] at h2
  exact_mod_cast h2

end GlobalTheory.Core.Ht2.StepRowsS
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetBlockBoundLeExpKernelBound

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.BlockNumber

theorem factor_eq_exp {a : ℕ} (nu : DomWeight a) (y : ℕ → ℚ) (b : ℕ) (L : ℝ) (h0 : ∀ l, 0 ≤ nu.w l)
    (hy : ∀ l : Fin a, ((nu.w l : ℤ) : ℚ) = y l) :
    (Real.exp L)⁻¹ ^ GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size nu * Real.exp 1 * (2 * (GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size nu : ℝ) + 2) ^ (2 * (a * b)) *
      Real.exp (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.ph (nu.w i : ℝ)) =
    Real.exp (((∑ i ∈ Finset.range a, Formalism.LatticeIndexTer.ph ((y i : ℚ) : ℝ)) - ((∑ i ∈ Finset.range a, y i : ℚ) : ℝ) * L) +
      (1 + 2 * ((a : ℝ) * b) * Real.log (2 * ((∑ i ∈ Finset.range a, y i : ℚ) : ℝ) + 2))) := by
  have hr : ∀ l : Fin a, ((y l : ℚ) : ℝ) = (nu.w l : ℝ) := fun l => by rw [← hy l]; simp
  have hs : ((∑ i ∈ Finset.range a, y i : ℚ) : ℝ) = (GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size nu : ℝ) := by
    rw [Finset.sum_range, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size]
    push_cast
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hr l]
    have := Int.toNat_of_nonneg (h0 l)
    exact_mod_cast this.symm
  have hp : (∑ i ∈ Finset.range a, Formalism.LatticeIndexTer.ph ((y i : ℚ) : ℝ)) = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.ph (nu.w i : ℝ) := by
    rw [Finset.sum_range (fun i => Formalism.LatticeIndexTer.ph ((y i : ℚ) : ℝ))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hr l]; rfl
  rw [hs, hp]
  set s := GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size nu
  have hpos : (0 : ℝ) < 2 * (s : ℝ) + 2 := by positivity
  have e1 : (Real.exp L)⁻¹ ^ s = Real.exp (-((s : ℝ) * L)) := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]; congr 1; ring
  have e2 : (2 * (s : ℝ) + 2) ^ (2 * (a * b)) = Real.exp (2 * ((a : ℝ) * b) * Real.log (2 * (s : ℝ) + 2)) := by
    conv_lhs => rw [← Real.exp_log hpos, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  rw [e1, e2, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1; ring

theorem sq_le_exp (C A g T : ℕ) (G r L : ℝ) (hG : 1 ≤ G) (hT : 1 ≤ T) (hr : 0 ≤ r) (hg : 1 ≤ g) (hA : g ≤ A) :
    (G ^ (C * A) * ((T : ℝ) * G) ^ (2 * (2 * g)) * Real.sqrt (3 * (2 * (g : ℝ) * r + 1) ^ g) * Real.exp (L / 2)) ^ 2 ≤
      Real.exp (L + ((g : ℝ) * Real.log (8 + 32 * (g : ℝ) * (r / 2)) + 2 * (((C : ℝ) + 4) * A * Real.log (G * T)))) := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hGT : 1 ≤ G * T := one_le_mul_of_one_le_of_one_le hG hT'
  have hx : (0 : ℝ) < 2 * (g : ℝ) * r + 1 := by positivity
  have h8 : (0 : ℝ) < 8 + 32 * (g : ℝ) * (r / 2) := by positivity
  have e1 : Real.exp ((g : ℝ) * Real.log (8 + 32 * (g : ℝ) * (r / 2))) = 8 ^ g * (2 * (g : ℝ) * r + 1) ^ g := by
    rw [Real.exp_nat_mul, Real.exp_log h8, ← mul_pow]; congr 1; ring
  have e2 : Real.exp (2 * (((C : ℝ) + 4) * A * Real.log (G * T))) = (G * T) ^ (2 * (C * A)) * (G * T) ^ (8 * A) := by
    rw [← pow_add]
    conv_rhs => rw [← Real.exp_log (show (0 : ℝ) < G * T by linarith), ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  have e3 : Real.exp (L / 2) ^ 2 = Real.exp L := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [Real.exp_add, Real.exp_add, e1, e2, mul_pow, mul_pow, mul_pow, e3, Real.sq_sqrt (by positivity), ← pow_mul, ← pow_mul]
  have b1 : G ^ (C * A * 2) ≤ (G * T) ^ (2 * (C * A)) := by
    rw [mul_comm (C * A) 2]
    exact pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_right (by linarith) hT') _
  have b2 : ((T : ℝ) * G) ^ (2 * (2 * g) * 2) ≤ (G * T) ^ (8 * A) := by
    rw [mul_comm (T : ℝ) G]
    exact pow_le_pow_right₀ hGT (by omega)
  have b3 : (3 : ℝ) ≤ 8 ^ g := by
    calc (3 : ℝ) ≤ 8 ^ 1 := by norm_num
      _ ≤ 8 ^ g := pow_le_pow_right₀ (by norm_num) hg
  have hG0 : 0 ≤ G := by linarith
  calc G ^ (C * A * 2) * ((T : ℝ) * G) ^ (2 * (2 * g) * 2) * (3 * (2 * (g : ℝ) * r + 1) ^ g) * Real.exp L
      ≤ (G * T) ^ (2 * (C * A)) * (G * T) ^ (8 * A) * (8 ^ g * (2 * (g : ℝ) * r + 1) ^ g) * Real.exp L := by gcongr
    _ = _ := by ring

theorem tmax_le_exp_kernelBound : ∀ C : ℕ, ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (N : NumDatum) (δ : Code N) (T : ℕ) (i : ℕ) (ι : Type) [Fintype ι] (pl : RPl N.R ≃ ι) (nu : ι → DomWeight (N.R.N i)) (logOm : RPl N.R → ℝ) (logTh : ℝ), i < N.R.m → 2 ≤ T → (∀ τ l, 0 ≤ (nu τ).w l) → (∀ (z : RPl N.R) (l : Fin (N.R.N i)), (((nu (pl z)).w l : ℤ) : ℚ) = N.nu δ (i + 1) z l) → GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.tmax (N.R.N (i + 1)) nu (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2) * ((T * (N.g 0 * N.g 1) : ℕ) : ℝ) ^ (2 * (2 * N.R.f * N.R.N i * N.R.N (i + 1))) * Real.sqrt (3 * (2 * ((N.R.f * N.R.N i * N.R.N (i + 1) : ℕ) : ℝ) * N.rd + 1) ^ (N.R.f * N.R.N i * N.R.N (i + 1))) * Real.exp (logTh / 2)) (fun τ => Real.exp (logOm (pl.symm τ))) ≤ Real.exp (kernelBound_sq N δ T CK (i + 1) logOm logTh 1 1 1 1) := by
  intro C
  refine ⟨(C : ℝ) + 4, by positivity, ?_⟩
  intro N δ T i ι _ pl nu logOm logTh hi hT h0 hy
  have hm := N.R.two_le_m
  have hk := N.R.m_add_three_le_k
  have ha : 1 ≤ N.R.N i := by unfold Ranks.N; omega
  have hb : 1 ≤ N.R.N (i + 1) := by unfold Ranks.N; omega
  have hf : 1 ≤ N.R.f := by
    have : 0 < N.R.ord := N.R.ord_pos
    unfold Ranks.f Ranks.n; omega
  have haN : N.R.N i ≤ N.Nm := by
    unfold NumDatum.Nm Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi.le) _
  have hbN : N.R.N (i + 1) ≤ N.Nm := by
    unfold NumDatum.Nm Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _
  have hg : 1 ≤ N.R.f * N.R.N i * N.R.N (i + 1) := Nat.mul_pos (Nat.mul_pos hf ha) hb
  have hA : N.R.f * N.R.N i * N.R.N (i + 1) ≤ N.R.f * N.R.m ^ 2 * N.Nm ^ 2 := by
    have h1 : 1 ≤ N.R.m ^ 2 := Nat.one_le_pow _ _ (by omega)
    calc N.R.f * N.R.N i * N.R.N (i + 1) = N.R.f * 1 * (N.R.N i * N.R.N (i + 1)) := by ring
      _ ≤ N.R.f * N.R.m ^ 2 * (N.Nm * N.Nm) := by gcongr
      _ = _ := by ring
  have hG : (1 : ℝ) ≤ (N.g 0 : ℝ) * N.g 1 :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast (N.g_prime 0).one_le) (by exact_mod_cast (N.g_prime 1).one_le)
  have hr : 0 ≤ N.rd := by unfold NumDatum.rd Formalism.HC.HostRaw.rd; positivity
  have key := sq_le_exp C _ _ T _ N.rd logTh hG (by omega) hr hg hA
  have hprod := fun z : RPl N.R => factor_eq_exp (nu (pl z)) (N.nu δ (i + 1) z) (N.R.N (i + 1)) (logOm z) (h0 _) (hy z)
  unfold GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.tmax
  rw [← pl.prod_comp]
  simp only [Equiv.symm_apply_apply]
  rw [Finset.prod_congr rfl fun z _ => hprod z, ← Real.exp_sum]
  have e1 : C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2 = C * (N.R.f * N.R.m ^ 2 * N.Nm ^ 2) := by ring
  have e2 : 2 * N.R.f * N.R.N i * N.R.N (i + 1) = 2 * (N.R.f * N.R.N i * N.R.N (i + 1)) := by ring
  have e3 : ((T * (N.g 0 * N.g 1) : ℕ) : ℝ) = (T : ℝ) * ((N.g 0 : ℝ) * N.g 1) := by push_cast; ring
  rw [e1, e2, e3]
  refine (mul_le_mul_of_nonneg_right key (Real.exp_pos _).le).trans (le_of_eq ?_)
  rw [← Real.exp_add]
  congr 1
  unfold kernelBound_sq NumDatum.nuAbs NumDatum.v
  simp only [Nat.add_sub_cancel, Finset.sum_add_distrib, Nat.cast_one, mul_one, Real.log_one]
  push_cast
  simp only [mul_assoc]
  ring

end GlobalTheory.BlockNumber
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetBlockBoundLeExpKernelBoundStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.exists_jetBlockBound_le_exp_kernelBound : ∀ C : ℕ, ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (N : NumDatum) (δ : Code N) (T : ℕ) (i : ℕ) (ι : Type) [Fintype ι] (pl : RPl N.R ≃ ι) (nu : ι → DomWeight (N.R.N i)) (logOm : RPl N.R → ℝ) (logTh : ℝ), i < N.R.m → 2 ≤ T → (∀ τ l, 0 ≤ (nu τ).w l) → (∀ (z : RPl N.R) (l : Fin (N.R.N i)), (((nu (pl z)).w l : ℤ) : ℚ) = N.nu δ (i + 1) z l) → GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.tmax (N.R.N (i + 1)) nu (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2) * ((T * (N.g 0 * N.g 1) : ℕ) : ℝ) ^ (2 * (2 * N.R.f * N.R.N i * N.R.N (i + 1))) * Real.sqrt (3 * (2 * ((N.R.f * N.R.N i * N.R.N (i + 1) : ℕ) : ℝ) * N.rd + 1) ^ (N.R.f * N.R.N i * N.R.N (i + 1))) * Real.exp (logTh / 2)) (fun τ => Real.exp (logOm (pl.symm τ))) ≤ Real.exp (kernelBound_sq N δ T CK (i + 1) logOm logTh 1 1 1 1) := by
  first | exact @GlobalTheory.BlockNumber.tmax_le_exp_kernelBound | exact GlobalTheory.BlockNumber.tmax_le_exp_kernelBound | (intros; apply GlobalTheory.BlockNumber.tmax_le_exp_kernelBound <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainKernelBoundAtEmbeddingAnyLevelPrime

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.Core.Ht2.KernelS

theorem kernel_le_sharp (hB : GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.BlockBound) (hT : FamilyTie) (hV : FamilyVectors) (hL : PeriodLattices)
    (hR : CosetRefinement) (hP : GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod) (C : ℕ) : ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ B : Base D D.host.ccK dl,
      FieldOfDefinition W sel mu cst u (ambOf s B χ cD) → ∀ i j, j = i + 1 → i < N.R.m →
      ∀ (L : Submodule (𝓞 X.E) (Sp X.E (N.R.N i))) (fr : Frs X.E (N.R.N i) (rowSG Pr sel mu))
        (L' : Submodule (𝓞 X.E) (Sp X.E (N.R.N j))) (fr' : Frs X.E (N.R.N j) (rowSG Pr sel mu)), IsSdLat L → IsSdLat L' →
      ∀ Ξ : HomE X.E (N.R.N i) (N.R.N j) → X.K, SmallDatum (Sall sel mu u) L L' (Pr.T u * (Pr.g 0 * Pr.g 1)) Ξ
        (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2)) →
      ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (hM : ThetaFieldData B cD s.σ₀ N.R M) (ρ : M →ₐ[ℚ] ℂ),
        CoefOpLe ((ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hM.1)) (W.lamTrue u i) (W.lamTrue u j)
          (kerOf (stepC W Ch sel mu cst (ambOf s B χ cD) u i (W.lamTrue u j)) (Sall sel mu u) (cAof sel mu cst)
            (cBof sel mu cst u) L fr L' fr' Ξ)
          (Real.exp (kernelBound_sq N δ (Pr.T u) CK j (fun z => logOmAt B cD M ρ (s.iT (pl z)))
            (logThAt B M ρ (N.R.N (j - 1)) (N.R.N j)) 1 1 1 1)) := by
  obtain ⟨CK, hCK, hnum⟩ := GlobalTheory.T.exists_jetBlockBound_le_exp_kernelBound C
  refine ⟨CK, hCK, ?_⟩
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H B hFD i j hj hi L fr L' fr' hL1 hL2 Ξ hΞ M _ hM ρ
  subst hj
  have H' := H
  obtain ⟨hHost, hWt, hCh, hAn, hmu, hsh, hI, hSz, hRows⟩ := H'
  obtain ⟨trd, -, -, -, tf, -, tE, -, tcc⟩ := GlobalTheory.T.numDatum_numbers_eq_host_of_compatible D N X s Pr hHost
  obtain ⟨-, -, -, -, hpsi, hadm, hX, hs, -, hPr, -, -, hg, -⟩ := hHost
  obtain ⟨-, -, -, hprod, hTodd, hgodd, hS⟩ := GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  obtain ⟨hstep, hnu⟩ := GlobalTheory.Core.Ht2.StepRowsS.weights_rows CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi
  have hcrv : StandardLatticesGL3.Crv D D.host.ccK dl := ⟨tcc, hAn.1⟩
  have hY := GlobalTheory.T.kernelConstant_exponents_finite D B.γ₀ B.kc
  have hev : ∀ l, Even (N.R.N l) := fun l => by
    unfold Ranks.N
    exact N.R.k_even.add ((N.R.t_odd.add_one).mul_left l)
  have hlt : N.R.N i < N.R.N (i + 1) := by
    unfold Ranks.N
    nlinarith
  obtain ⟨hAdm, hbase⟩ := GlobalTheory.T.normalisedFamily_standardLattices_eq_baseVector D _ dl B χ hAn.2.1 (hV D _ dl B χ hadm hpsi tcc hAn.1 hAn.2.1 hY) _ _ (hev i) (hev (i + 1))
  have hE0 := hT D _ dl B χ hadm hpsi tcc hAn.1 hAn.2.1 hY _ B.t0 _ _ _ _ hAdm
  rw [hbase] at hE0
  have hgpos : 0 < Pr.g 0 * Pr.g 1 := Nat.mul_pos (hPr.g_prime 0).pos (hPr.g_prime 1).pos
  have hfpos : 0 < N.R.f := by
    unfold Ranks.f Ranks.n
    have := N.R.ord_pos
    omega
  have hBpos := hI.cst_ok.B_pos
  have hcA : cAof sel mu cst = (Pr.g 0 * Pr.g 1) ^ (N.R.f * cst.A) := by unfold cAof; rw [hprod, pow_mul]
  have hcB : cBof sel mu cst u = Pr.T u * (Pr.g 0 * Pr.g 1) * (Pr.g 0 * Pr.g 1) ^ (N.R.f * cst.B - 1) := by
    unfold cBof
    have h1 : N.R.f * cst.B = (N.R.f * cst.B - 1) + 1 := by
      have := Nat.mul_pos hfpos hBpos
      omega
    rw [hprod, ← pow_mul]
    conv_lhs => rw [h1]
    ring
  have hodd : Odd (cAof sel mu cst * cBof sel mu cst u) := by
    have h1 : Odd (Pr.g 0 * Pr.g 1) := (hgodd 0).mul (hgodd 1)
    rw [hcA, hcB]
    exact h1.pow.mul ((hTodd.mul h1).mul h1.pow)
  have hInd := hR X (ambOf s B χ cD) _ _ (Sall sel mu u) _ hX.ok (fun P hP => (hS P hP).2) hodd
    (hL D X s _ dl B χ cD hX.ok hs hadm hpsi tcc hAn.1 hAn.2.1 hAn.2.2 hY _ _ (Sall sel mu u) (hev i) (hev (i + 1))
      (fun P hP => (hS P hP).1) (GlobalTheory.T.periodLatticeIdeal_trivial_at_badPrimes CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H B))
  have hJ := hFD i hi
  have hc0 : ∀ τ, cD τ ≠ 0 := (GlobalTheory.T.mean_logMetric_generator_eq_meanPeriod D _ dl cD hcrv (hP D _ dl tcc hAn.1) hAn.2.2).1
  have hsc : ‖((ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hM.1))
      (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) L fr *
        (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) L' fr')⁻¹)‖ ≤ 1 := by
    rw [map_mul, map_inv₀, norm_mul, norm_inv]
    rcases GlobalTheory.ScalarModulusS.norm_muInvDet_zero_or_one CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi _ L fr
      ((ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hM.1)) with h1 | h1 <;>
    rcases GlobalTheory.ScalarModulusS.norm_muInvDet_zero_or_one CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi _ L' fr'
      ((ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hM.1)) with h2 | h2 <;> rw [h1, h2] <;> norm_num
  unfold stepC
  rw [hcB] at hInd hJ ⊢
  have key := block hB D X s _ dl B χ cD _ hX.ok hs hcrv B.t0 hc0 _ _ hlt ((hev i).mul_right _) hE0
    (W.lamTrue u i) (W.nuW u (i + 1)) (W.lamTrue u (i + 1)) hstep (Sall sel mu u) (rowSG Pr sel mu) (cAof sel mu cst)
    (Pr.T u * (Pr.g 0 * Pr.g 1)) ((Pr.g 0 * Pr.g 1) ^ (N.R.f * cst.B - 1)) (by rw [hcA]; positivity)
    (Nat.mul_pos (hPr.T_prime u).pos hgpos) (by positivity) hInd hJ sel (mUof Ch mu i) (muAt Ch sel mu cst i) L fr L' fr' hL1 hL2
    Ξ _ hΞ M hM.1 ρ hM.2.1 hM.2.2.1 (hM.2.2.2 i hi) hsc
  have hn := hnum N δ (Pr.T u) i X.Tau pl (W.nuW u (i + 1)) (fun z => logOmAt B cD M ρ (s.iT (pl z)))
    (logThAt B M ρ (N.R.N i) (N.R.N (i + 1))) hi (hPr.T_prime u).two_le (fun τ => (hstep τ).1) hnu
  intro x
  refine (key x).trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · refine le_trans (le_of_eq ?_) hn
    simp only [supConst, tf, tE, ← trd, hg, Equiv.apply_symm_apply]
  · exact sqAt_nonneg _ _ _

end GlobalTheory.Core.Ht2.KernelS
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainKernelBoundAtEmbeddingAnyLevelPrimeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.chainKernel_bound_at_embedding_anyLevelPrime : GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.BlockBound → FamilyTie → FamilyVectors → PeriodLattices → CosetRefinement → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod → ∀ C : ℕ, ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ B : Base D D.host.ccK dl, FieldOfDefinition W sel mu cst u (ambOf s B χ cD) → ∀ i j, j = i + 1 → i < N.R.m → ∀ (L : Submodule (𝓞 X.E) (Sp X.E (N.R.N i))) (fr : Frs X.E (N.R.N i) (rowSG Pr sel mu)) (L' : Submodule (𝓞 X.E) (Sp X.E (N.R.N j))) (fr' : Frs X.E (N.R.N j) (rowSG Pr sel mu)), IsSdLat L → IsSdLat L' → ∀ Ξ : HomE X.E (N.R.N i) (N.R.N j) → X.K, SmallDatum (Sall sel mu u) L L' (Pr.T u * (Pr.g 0 * Pr.g 1)) Ξ (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2)) → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (hM : ThetaFieldData B cD s.σ₀ N.R M) (ρ : M →ₐ[ℚ] ℂ), CoefOpLe ((ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hM.1)) (W.lamTrue u i) (W.lamTrue u j) (kerOf (stepC W Ch sel mu cst (ambOf s B χ cD) u i (W.lamTrue u j)) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) L fr L' fr' Ξ) (Real.exp (kernelBound_sq N δ (Pr.T u) CK j (fun z => logOmAt B cD M ρ (s.iT (pl z))) (logThAt B M ρ (N.R.N (j - 1)) (N.R.N j)) 1 1 1 1))  := by
  first | exact @GlobalTheory.Core.Ht2.KernelS.kernel_le_sharp | exact GlobalTheory.Core.Ht2.KernelS.kernel_le_sharp | (intros; apply GlobalTheory.Core.Ht2.KernelS.kernel_le_sharp <;> assumption)
end
end
