module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MovedVacuumMemThetaFunctionsAndMoves
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.EqOffBound
public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.Assemble
public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.SplitElementExistsHolds
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.DescentCore
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelFunctionsCommonLinearOperatorOffSplitPrimeStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOffSplitOfEqOffSplitPrime

section

@[expose] public section

noncomputable section

namespace GlobalTheory.EqOffSplitOfSplit

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

theorem isSplit_conj (D : D7) {P Q : HeightOneSpectrum (𝓞 D.host.E)} (hP : GL3Theta.SplitP D P)
    (hQ : ∀ x : 𝓞 D.host.E, x ∈ Q.asIdeal ↔ Formalism.L2.PairingIndexBounds.Rec.cO D x ∈ P.asIdeal) : GL3Theta.SplitP D Q := by
  obtain ⟨a, b, hab, ha, hb⟩ := hP
  have hb' : b = Formalism.L2.PairingIndexBounds.Rec.cO D a := Subtype.ext (hab.trans rfl)
  refine ⟨b, a, ?_, ?_, ?_⟩
  · rw [hab]; exact (Formalism.L2.PairingIndexBounds.Rec.conj_conj' D (a : D.host.E)).symm
  · rw [hQ, hb', Formalism.L2.PairingIndexBounds.Rec.cO_cO]; exact ha
  · rw [hQ, ← hb']; exact hb

theorem eqOffSplit_of_eqOff : ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ)
    (L L₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
    GL3Theta.SplitP D P → GL3Theta.EqOff D P L L₀ → GL3Theta.EqOffSplit D L L₀ := by
  intro D P n L L₀ hP hoff
  obtain ⟨m, hm⟩ := hoff
  obtain ⟨x, hx0, hxP, hxM⟩ := Formalism.L2.PairingIndexBounds.Rec.genPow D P
  have hc0 : ∀ y : 𝓞 D.host.E, y ≠ 0 → Formalism.L2.PairingIndexBounds.Rec.cO D y ≠ 0 := fun y hy h => hy (by
    rw [← Formalism.L2.PairingIndexBounds.Rec.cO_cO D y, h, map_zero])
  have hg0 : x ^ m ≠ 0 := pow_ne_zero m hx0
  obtain ⟨h1, h2⟩ := hm (x ^ m) (Formalism.L2.PairingIndexBounds.Rec.cO D (x ^ m)) rfl (Ideal.pow_mem_pow hxP m)
  refine ⟨x ^ m * Formalism.L2.PairingIndexBounds.Rec.cO D (x ^ m), mul_ne_zero hg0 (hc0 _ hg0), fun Q hQ => ?_, h1, h2⟩
  rcases Q.isPrime.mem_or_mem hQ with h | h
  · have e : P.asIdeal = Q.asIdeal := hxM _ Q.isPrime (Q.isPrime.mem_of_pow_mem m h)
    have e' : P = Q := HeightOneSpectrum.ext e
    exact e' ▸ hP
  · rw [map_pow] at h
    have h3 : Formalism.L2.PairingIndexBounds.Rec.cO D x ∈ Q.asIdeal := Q.isPrime.mem_of_pow_mem m h
    have e : P.asIdeal = (Formalism.L2.PairingIndexBounds.Rec.cQ D Q).asIdeal :=
      hxM _ (Formalism.L2.PairingIndexBounds.Rec.cQ D Q).isPrime ((Formalism.L2.PairingIndexBounds.Rec.mem_cQ D Q x).2 h3)
    refine isSplit_conj D hP fun y => ?_
    rw [e, Formalism.L2.PairingIndexBounds.Rec.mem_cQ, Formalism.L2.PairingIndexBounds.Rec.cO_cO]

end GlobalTheory.EqOffSplitOfSplit
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOffSplitOfEqOffSplitPrimeStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

theorem _root_.GlobalTheory.T.eqOffSplit_of_eqOff_splitPrime : ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ) (L L₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), GL3Theta.SplitP D P → GL3Theta.EqOff D P L L₀ → GL3Theta.EqOffSplit D L L₀ := by
  first | exact @GlobalTheory.EqOffSplitOfSplit.eqOffSplit_of_eqOff | exact GlobalTheory.EqOffSplitOfSplit.eqOffSplit_of_eqOff | (intros; apply GlobalTheory.EqOffSplitOfSplit.eqOffSplit_of_eqOff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaRelationOfIndicatorRelationSplit

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

namespace GlobalTheory.KerRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem eqOffSplit_of_eqOff : ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ) (L L₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), GL3Theta.SplitP D P → GL3Theta.EqOff D P L L₀ → GL3Theta.EqOffSplit D L L₀ := GlobalTheory.T.eqOffSplit_of_eqOff_splitPrime

theorem kerTh_common : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → B.LatAll → B.VecP χ → ∀ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), 0 < cl → (∀ Q ∈ SS, Formalism.L2.Col.conjPrime₂ Q ∉ SS) → ∀ (a b : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)), GL3Theta.SplitP D P → P ∉ SS → Formalism.L2.Col.conjPrime₂ P ∉ SS → ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((cl : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.Col.conjPrime₂ P).asIdeal → ∀ (N₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), TaylorLogMetric.admitted D a b N₀ N₀' → DatLoc D cc SS cl N₀ N₀' Ξ → ∀ (ι : Type) [Fintype ι] (N : ι → Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : ι → Submodule (𝓞 D.host.E) (Fin b → D.host.E)), (∀ i, TaylorLogMetric.admitted D a b (N i) (N' i) ∧ GL3Theta.EqOff D P (N i) N₀ ∧ GL3Theta.EqOff D P (N' i) N₀') → ∃ T : (TaylorLogMetric.VC D a b → ℂ) →ₗ[ℂ] (TaylorLogMetric.VC D a b → ℂ), ∀ i, kerTh B χ SS cl (N i) (N' i) Ξ = T (B.eNat χ a b (N i) (N' i)) := GlobalTheory.T.kernelFunctions_common_linearOperator_off_splitPrime

theorem eqOffSplit_refl (D : D7) {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : GL3Theta.EqOffSplit D L L :=
  ⟨1, one_ne_zero, fun Q hQ => (Q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hQ isUnit_one)).elim,
    fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩

theorem eqOffSplit_symm {D : D7} {n : ℕ} {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (h : GL3Theta.EqOffSplit D L₁ L₂) : GL3Theta.EqOffSplit D L₂ L₁ := by
  obtain ⟨a, ha0, hsa, ha1, ha2⟩ := h
  exact ⟨a, ha0, hsa, ha2, ha1⟩

theorem mem_Th_const_mul (D : D7) (T : TaylorLogMetric.Tor D) {a b : ℕ} {L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)} {F : TaylorLogMetric.VC D a b → ℂ} (hF : F ∈ TaylorLogMetric.Th D T L L') (k : ℂ) :
    (fun z => k * F z) ∈ TaylorLogMetric.Th D T L L' := by
  refine ⟨hF.1.const_mul k, fun x hx z => ?_⟩
  have := hF.2 x hx z
  simp only [TaylorLogMetric.U] at this ⊢
  rw [← this]; ring

theorem chiFac_ne_zero (D : D7) {χ : TaylorLogMetric.IdE D → ℂ} (hχ : TaylorLogMetric.IsChi D χ) {a b : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}
    (h : StandardLatticesGL3.SD D L) (h' : StandardLatticesGL3.SD D L') : Base.chiFac χ a b L L' ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (GlobalTheory.ThetaMove.Moved.chi_detId_ne_zero hχ (GlobalTheory.ThetaMove.Moved.sd_stdL D a) h))
    (zpow_ne_zero _ (GlobalTheory.ThetaMove.Moved.chi_detId_ne_zero hχ (GlobalTheory.ThetaMove.Moved.sd_stdL D b) h'))

theorem thMoved_move_right (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) {a b : ℕ}
    (hχ : TaylorLogMetric.IsChi D χ) (hE : B.EqP χ) (ha : Even a) (hb : Even b) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (L' L'' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (h : StandardLatticesGL3.SD D L) (h' : StandardLatticesGL3.SD D L') (h'' : StandardLatticesGL3.SD D L'') :
    B.thMoved a b L L'' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L L'') (B.thMoved a b L L') := by
  funext z
  have e : Base.chiFac χ a b L L'' * B.thMoved a b L L'' z = χ (TaylorLogMetric.detId D L' L'') ^ (-((a / 2 : ℕ) : ℤ)) *
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L L'')
        (fun w => Base.chiFac χ a b L L' * B.thMoved a b L L' w) z :=
    congrFun (hE.2.1 a b ⟨L, h⟩ ⟨L', h'⟩ ⟨L'', h''⟩ ha hb) z
  have f : Base.chiFac χ a b L L'' = χ (TaylorLogMetric.detId D L' L'') ^ (-((a / 2 : ℕ) : ℤ)) * Base.chiFac χ a b L L' := by
    unfold Base.chiFac
    rw [GlobalTheory.ThetaMove.Moved.chi_detId_mul hχ (GlobalTheory.ThetaMove.Moved.sd_stdL D b) h' h'', mul_zpow]
    ring
  rw [GlobalTheory.ThetaMove.Moved.iop_mul, ← mul_assoc, ← f] at e
  exact mul_left_cancel₀ (chiFac_ne_zero D hχ h h'') e

theorem thMoved_move_left (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) {a b : ℕ}
    (hχ : TaylorLogMetric.IsChi D χ) (hE : B.EqP χ) (ha : Even a) (hb : Even b) (L L₁ : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (h : StandardLatticesGL3.SD D L) (h₁ : StandardLatticesGL3.SD D L₁) (h' : StandardLatticesGL3.SD D L') :
    B.thMoved a b L₁ L' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L') (B.thMoved a b L L') := by
  funext z
  have e : Base.chiFac χ a b L₁ L' * B.thMoved a b L₁ L' z = χ (TaylorLogMetric.detId D L L₁) ^ (((b / 2 : ℕ) : ℤ)) *
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L')
        (fun w => Base.chiFac χ a b L L' * B.thMoved a b L L' w) z :=
    congrFun (hE.2.2 a b ⟨L, h⟩ ⟨L₁, h₁⟩ ⟨L', h'⟩ ha hb) z
  have f : Base.chiFac χ a b L₁ L' = χ (TaylorLogMetric.detId D L L₁) ^ (((b / 2 : ℕ) : ℤ)) * Base.chiFac χ a b L L' := by
    unfold Base.chiFac
    rw [GlobalTheory.ThetaMove.Moved.chi_detId_mul hχ (GlobalTheory.ThetaMove.Moved.sd_stdL D a) h h₁, mul_zpow]
    ring
  rw [GlobalTheory.ThetaMove.Moved.iop_mul, ← mul_assoc, ← f] at e
  exact mul_left_cancel₀ (chiFac_ne_zero D hχ h₁ h') e

theorem kerTh_relation_of_indicator : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → TaylorLogMetric.IsChi D χ → B.LatAll → B.VecP χ → B.EqP χ → GL3Theta.modelXi D → GL3Theta.movesCompose D → ∀ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), 0 < cl → (∀ Q ∈ SS, Formalism.L2.Col.conjPrime₂ Q ∉ SS) → ∀ (a b : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)), GL3Theta.SplitP D P → P ∉ SS → Formalism.L2.Col.conjPrime₂ P ∉ SS → ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((cl : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.Col.conjPrime₂ P).asIdeal → ∀ (N₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), TaylorLogMetric.admitted D a b N₀ N₀' → DatLoc D cc SS cl N₀ N₀' Ξ → ∀ (ι : Type) [Fintype ι] (N : ι → Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : ι → Submodule (𝓞 D.host.E) (Fin b → D.host.E)), (∀ i, TaylorLogMetric.admitted D a b (N i) (N' i) ∧ GL3Theta.EqOff D P (N i) N₀ ∧ GL3Theta.EqOff D P (N' i) N₀') → ∀ c : ι → ℂ, (∑ i, c i • Set.indicator (GL3Theta.YP D P (N i) (N' i) : Set (Matrix (Fin b) (Fin a) (GL3Theta.EP D P))) (1 : Matrix (Fin b) (Fin a) (GL3Theta.EP D P) → ℂ)) = 0 → ∀ z, ∑ i, c i * (((Real.sqrt (GL3Theta.volP (GL3Theta.YP D P N₀ N₀') (GL3Theta.YP D P (N i) (N' i))) : ℝ) : ℂ) * (Base.chiFac χ a b (N i) (N' i))⁻¹ * kerTh B χ SS cl (N i) (N' i) Ξ z) = 0 := by
  intro D cc δ B χ hcc hδ hδ0 hχ hL hV hE hModel hMoves SS cl hcl hSS a b P hP hPS hPS' hcP hcP' N₀ N₀' Ξ hA0 hD ι _ N N' hN c hrel z
  obtain ⟨T, hT⟩ := kerTh_common D cc δ B χ hcc hδ hδ0 hL hV SS cl hcl hSS a b P hP hPS hPS' hcP hcP' N₀ N₀' Ξ hA0 hD ι N N' hN
  obtain ⟨ha, hb, h0, h0'⟩ := hA0
  have hth0 : B.thMoved a b N₀ N₀' ∈ TaylorLogMetric.Th D (TaylorLogMetric.tor0 D cc δ) N₀ N₀' := by
    have hm := mem_Th_const_mul D (TaylorLogMetric.tor0 D cc δ) (hV a b N₀ N₀' ⟨ha, hb, h0, h0'⟩).1 (Base.chiFac χ a b N₀ N₀')⁻¹
    convert hm using 1
    funext w
    show _ = _ * (Base.chiFac χ a b N₀ N₀' * _)
    rw [← mul_assoc, inv_mul_cancel₀ (chiFac_ne_zero D hχ h0 h0'), one_mul]
  obtain ⟨Xi, -, hXi⟩ := hModel cc δ hcc hδ a b N₀ N₀' ⟨ha, hb, h0, h0'⟩ P hP _ hth0
  have hmove : ∀ i, B.thMoved a b (N i) (N' i) =
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor N₀ N₀') (TaylorLogMetric.La D B.tor (N i) (N' i)) (B.thMoved a b N₀ N₀') := by
    intro i
    obtain ⟨⟨-, -, hi, hi'⟩, ho, ho'⟩ := hN i
    rw [thMoved_move_right D cc δ B χ hχ hE ha hb (N i) N₀' (N' i) hi h0' hi',
      thMoved_move_left D cc δ B χ hχ hE ha hb N₀ (N i) N₀' h0 hi h0']
    exact hMoves cc δ hcc hδ a b N₀ (N i) (N i) N₀' N₀' (N' i) ⟨ha, hb, h0, h0'⟩ ⟨ha, hb, hi, h0'⟩ ⟨ha, hb, hi, hi'⟩
      (eqOffSplit_symm (eqOffSplit_of_eqOff D P _ _ _ hP ho)) (eqOffSplit_refl D _) (eqOffSplit_refl D _)
      (eqOffSplit_symm (eqOffSplit_of_eqOff D P _ _ _ hP ho')) _ hth0
  have key : ∀ i, ((Real.sqrt (GL3Theta.volP (GL3Theta.YP D P N₀ N₀') (GL3Theta.YP D P (N i) (N' i))) : ℝ) : ℂ) *
      (Base.chiFac χ a b (N i) (N' i))⁻¹ * kerTh B χ SS cl (N i) (N' i) Ξ z =
      T (Xi (Set.indicator (GL3Theta.YP D P (N i) (N' i) : Set (Matrix (Fin b) (Fin a) (GL3Theta.EP D P))) 1)) z := by
    intro i
    obtain ⟨⟨-, -, hi, hi'⟩, -, -⟩ := hN i
    set s : ℂ := ((Real.sqrt (GL3Theta.volP (GL3Theta.YP D P N₀ N₀') (GL3Theta.YP D P (N i) (N' i))) : ℝ) : ℂ) with hs
    set X := Xi (Set.indicator (GL3Theta.YP D P (N i) (N' i) : Set (Matrix (Fin b) (Fin a) (GL3Theta.EP D P))) 1) with hX
    have hm : B.thMoved a b (N i) (N' i) = fun w => s⁻¹ * X w := by
      rw [hmove i, hXi (N i) (N' i) ⟨ha, hb, hi, hi'⟩ (hN i).2.1 (hN i).2.2]
      funext w
      push_cast
      rfl
    have he : B.eNat χ a b (N i) (N' i) = (Base.chiFac χ a b (N i) (N' i) * s⁻¹) • X := by
      funext w
      show Base.chiFac χ a b (N i) (N' i) * B.thMoved a b (N i) (N' i) w = _
      rw [hm, Pi.smul_apply, smul_eq_mul, mul_assoc]
    have hs0 : s ≠ 0 := by
      intro h0s
      apply (hV a b (N i) (N' i) ⟨ha, hb, hi, hi'⟩).2.1
      rw [he, h0s, inv_zero, mul_zero, zero_smul]
    rw [hT i, he, map_smul, Pi.smul_apply, smul_eq_mul]
    field_simp [chiFac_ne_zero D hχ hi hi']
  simp_rw [key]
  have hsum := congrArg (fun f => T (Xi f) z) hrel

  simp only [map_sum, map_smul, map_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hsum
  exact hsum

end GlobalTheory.KerRel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaRelationOfIndicatorRelationSplitStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

theorem _root_.GlobalTheory.T.kernelTheta_relation_of_indicator_relation_split : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → TaylorLogMetric.IsChi D χ → B.LatAll → B.VecP χ → B.EqP χ → GL3Theta.modelXi D → GL3Theta.movesCompose D → ∀ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), 0 < cl → (∀ Q ∈ SS, Formalism.L2.Col.conjPrime₂ Q ∉ SS) → ∀ (a b : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)), GL3Theta.SplitP D P → P ∉ SS → Formalism.L2.Col.conjPrime₂ P ∉ SS → ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((cl : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.Col.conjPrime₂ P).asIdeal → ∀ (N₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), TaylorLogMetric.admitted D a b N₀ N₀' → DatLoc D cc SS cl N₀ N₀' Ξ → ∀ (ι : Type) [Fintype ι] (N : ι → Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : ι → Submodule (𝓞 D.host.E) (Fin b → D.host.E)), (∀ i, TaylorLogMetric.admitted D a b (N i) (N' i) ∧ GL3Theta.EqOff D P (N i) N₀ ∧ GL3Theta.EqOff D P (N' i) N₀') → ∀ c : ι → ℂ, (∑ i, c i • Set.indicator (GL3Theta.YP D P (N i) (N' i) : Set (Matrix (Fin b) (Fin a) (GL3Theta.EP D P))) (1 : Matrix (Fin b) (Fin a) (GL3Theta.EP D P) → ℂ)) = 0 → ∀ z, ∑ i, c i * (((Real.sqrt (GL3Theta.volP (GL3Theta.YP D P N₀ N₀') (GL3Theta.YP D P (N i) (N' i))) : ℝ) : ℂ) * (Base.chiFac χ a b (N i) (N' i))⁻¹ * kerTh B χ SS cl (N i) (N' i) Ξ z) = 0 := by
  first | exact @GlobalTheory.KerRel.kerTh_relation_of_indicator | exact GlobalTheory.KerRel.kerTh_relation_of_indicator | (intros; apply GlobalTheory.KerRel.kerTh_relation_of_indicator <;> assumption)
end
end
