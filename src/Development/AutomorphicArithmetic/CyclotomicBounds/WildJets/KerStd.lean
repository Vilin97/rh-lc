module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfValuationLeOne
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
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.JetInt
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.JetOpMulTab
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelAtPrimeEqSumTorsionTranslates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLineStatement
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JetsTorsionTranslatesCmThetaProductStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.BdLoss

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.bdLoss :
    ∀ (D : D7) (w : PlL D) (l : ℕ) [Fact l.Prime], (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → ∀ (z : ℂ) (B : ℝ), z ∈ Set.range D.what₂.embLL →
      (∀ lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[l], GlobalTheory.NormSum.Term.Bd lam ((l : ℝ) ^ B) z) → LossLe w z ((vw w ((l : ℕ) : D.what₂.LL) : ℝ) * B) := by
  intro D w l _ hl z B hz hB
  obtain ⟨y, rfl⟩ := hz
  refine ⟨y, rfl, ?_⟩
  by_cases hy : y = 0
  · exact Or.inl hy
  · right
    have key := GlobalTheory.PadicPlaceBound.neg_mul_vw_le_vw D.what₂.LL D.what₂.embLL y l w B hy hl
      (fun lam => (hB lam).2)
    rw [mul_comm] at key
    exact key
end
end

-- Source module: Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.CmbIop

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators


open GlobalTheory.NormSum.KernelAt in
theorem UpperTheory.WildA.cmbIop :
    ∀ (D : D7), Inp D → ∀ (cc : Ideal (𝓞 D.host.K)), cc = ⊤ → ∀ (δ t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 →
      ∀ (a b : ℕ) (e0 : VC D a b → ℂ), oddE0 D cc δ t0 a b e0 →
      ∀ (Ls : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), SD D Ls → SD D Lt →
      ∀ (l : ℕ) [Fact l.Prime] (lam : Qbar →+* ℂ_[l]), EqAt D l Ls (stdL D a) → EqAt D l Lt (stdL D b) → ∀ k : ℕ, 0 < k →
      ∃ (β : Fin (fF D * a * b) → Matrix (Fin b) (Fin a) D.host.E) (M : ℕ), OnB D β ∧ LocBasis D l (YYl D (stdL D a) (stdL D b)) β ∧
        0 < M ∧ Nat.Coprime M l ∧ ∀ s : VC D a b, k • s ∈ La D (tor0 D cc δ) Ls Lt →
          KernelAt.Cmb D (tor0 D cc δ) lam (LaB D (tor0 D cc δ) β) (pullB D (tor0 D cc δ) β (GL3Theta.th0 (lamOf D cc δ) t0)) (M * k) 1
            (U D (tor0 D cc δ) s (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0)) := by
  intro D hI cc hcc δ t0 hC hT a d e0 hvac Ls Lt hLs hLt p _ lam hEs hEt Q hQ
  subst hcc
  have hp : p.Prime := Fact.out
  obtain ⟨s₁, hs₁, -, hs₁a⟩ := hEs
  obtain ⟨s₂, hs₂, hs₂a, -⟩ := hEt
  have hLa := smul_mem_La ⊤ δ (smul_mem_YYl (smul_mem_homL hs₁a hs₂a))
  have hsp : Nat.Coprime (s₂ * s₁) p := Nat.Coprime.mul_left hs₂ hs₁
  obtain ⟨-, -, -, -, hfg, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hI.g1 ⊤ δ hC a d _
    (Or.inr ⟨Ls, Lt, hLs, hLt, rfl⟩)
  have hi₁ := coprime_index (La0 D (tor0 D ⊤ δ) a d) _ hfg _ p hp hsp hLa
  obtain ⟨b, ε, hb, hloc, hε, hεn, hi₀, he0⟩ := hvac.2.2.2.2 p lam (by simp)
  obtain ⟨-, -, hB, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hI.g1 ⊤ δ hC a d _ (Or.inl ⟨_, b, hb, rfl⟩)
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = ((LaB D (tor0 D ⊤ δ) b).addSubgroupOf (La0 D (tor0 D ⊤ δ) a d)).index := ⟨_, rfl⟩
  have hMp : Nat.Coprime (n₀ * (s₂ * s₁)) p := Nat.Coprime.mul_left (hn₀ ▸ hi₀) hsp
  have hM0 : n₀ * (s₂ * s₁) ≠ 0 := by
    intro h0
    rw [h0, Nat.coprime_zero_left] at hMp
    exact hp.one_lt.ne' hMp
  have hn : n₀ * (s₂ * s₁) * Q ≠ 0 := mul_ne_zero hM0 hQ.ne'
  have a0 : ∀ x ∈ La0 D (tor0 D ⊤ δ) a d, n₀ • x ∈ LaB D (tor0 D ⊤ δ) b := fun x hx => by
    rw [hn₀]
    exact ((LaB D (tor0 D ⊤ δ) b).addSubgroupOf (La0 D (tor0 D ⊤ δ) a d)).nsmul_index_mem ⟨x, hx⟩
  have a1 : ∀ x ∈ La D (tor0 D ⊤ δ) Ls Lt, (n₀ * (s₂ * s₁)) • x ∈ LaB D (tor0 D ⊤ δ) b := fun x hx => by
    rw [mul_smul]
    exact a0 _ (hLa x hx)
  have c0 : Cmb D (tor0 D ⊤ δ) lam (LaB D (tor0 D ⊤ δ) b) (pullB D (tor0 D ⊤ δ) b (GL3Theta.th0 (lamOf D ⊤ δ) t0))
      (n₀ * (s₂ * s₁) * Q) (1 * 1) e0 := by
    rw [he0]
    refine Cmb.smul ⟨hε, ?_⟩ (Cmb.iop hn hB hi₀ (fun x hx => ?_) Cmb.base)
    · rw [lamC, dite_eq_left hε] at hεn
      exact hεn.le
    · rw [mul_assoc n₀, mul_comm n₀, mul_smul]
      exact AddSubgroup.nsmul_mem _ (a0 x hx) _
  have c1 := Cmb.iop hn hB hi₁ (fun x hx => by
    rw [mul_comm _ Q, mul_smul]
    exact AddSubgroup.nsmul_mem _ (a1 x hx) _) c0
  rw [one_mul] at c1
  refine ⟨b, n₀ * (s₂ * s₁), hb, hloc, Nat.pos_of_ne_zero hM0, hMp, fun s hs => ?_⟩
  refine Cmb.transl hn hB ?_ c1
  rw [mul_smul]
  exact a1 _ hs
end
end

-- Source module: Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.CmbJet

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

open GlobalTheory.NormSum.Term in
theorem UpperTheory.WildA.cmbJet :
    ∀ (D : D7), Inp D → ∀ (S : Finset ℕ) (dl : ℕ → ℝ), Letters D S dl → ∀ (cc : Ideal (𝓞 D.host.K)), cc = ⊤ → ∀ (δ t0 : ℂ), Crv D cc δ →
      GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a b r : ℕ) (l : ℕ) [Fact l.Prime] (lam : Qbar →+* ℂ_[l])
      (β : Fin r → Matrix (Fin b) (Fin a) D.host.E), OnB D β → LocBasis D l (YYl D (stdL D a) (stdL D b)) β →
      ∀ (n : ℕ), 0 < n → (l ∣ n → SplitIn D l) → ∀ (C : ℝ), 0 ≤ C → ∀ G : VC D a b → ℂ,
      KernelAt.Cmb D (tor0 D cc δ) lam (LaB D (tor0 D cc δ) β) (pullB D (tor0 D cc δ) β (GL3Theta.th0 (lamOf D cc δ) t0)) n C G →
      ∀ mon : GL3Theta.Idx D a b →₀ ℕ,
        Term.Bd lam (C * (l : ℝ) ^ ((mon.degree : ℝ) * (dl l + (if l = D.host.d then 1 / 4 else 0) + (padicValNat l n : ℝ))))
          (GL3Theta.applyAt0 D (MvPolynomial.monomial mon 1) G) := by
  intro D hI S dl hL cc hcc δ t0 hC ht a b r l _ lam β hb hloc n hn hsp C hC0 G hG mon
  subst hcc
  obtain ⟨k, c, s, hs, hr, hF⟩ := hG.out
  have hp : l.Prime := Fact.out
  have hp0 : (0 : ℝ) < l := by exact_mod_cast hp.pos
  have hN := norm_natCast_inv l hn.ne'
  have he0 : 0 ≤ (if l = D.host.d then (l : ℝ) ^ (((mon.degree : ℕ) : ℝ) / 4) else 1) := by
    split_ifs <;> positivity
  have hmon : (MvPolynomial.monomial mon 1 : MvPolynomial (GL3Theta.Idx D a b) ℂ) =
      MvPolynomial.map (Int.castRingHom ℂ) (MvPolynomial.monomial mon 1) := by
    rw [MvPolynomial.map_monomial, map_one (Int.castRingHom ℂ)]
  have hcol := rpow_collect hp0 (l = D.host.d) mon.degree 0 (dl l) (padicValNat l n : ℝ)
  rw [pow_zero, one_mul, Nat.cast_zero, zero_mul, add_zero] at hcol
  rw [← hcol, mul_left_comm, hmon, hF]
  refine bd_applyAt0 (lam := lam) D (by positivity) _ _
    (MvPolynomial.isHomogeneous_monomial _ rfl) fun f => ?_
  refine bd_coord D (by positivity) (by positivity) (tor0 D ⊤ δ) (fun _ _ => rfl)
    (YYl D (stdL D a) (stdL D b)) (hL.2.2.2.2 l lam a b) _ (fun y hy => ?_) f
  rw [iteratedFDeriv_comb _ (fun i => (c i : ℂ))
    (fun i => U D (tor0 D ⊤ δ) (s i) (pullB D (tor0 D ⊤ δ) β (GL3Theta.th0 (lamOf D ⊤ δ) t0))) fun i =>
    contDiff_U_pullB D _ β _ (differentiable_evenTheta D ⊤ δ t0 hC) (s i) _]
  refine Bd.sum (by positivity) _ _ fun i _ => ?_
  refine (Bd.coe (hr i)).mul ?_
  have := GlobalTheory.T.jets_torsion_translates_cm_theta_product D hI l lam ⊤ δ hC (by simp) t0 ht a b _ β hb hloc (s i) n
    hn (hs i) hsp _ y hy
  rw [hN] at this
  exact this
end
end

-- Source module: Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.TabBd

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem UpperTheory.WildA.tabBd :
    ∀ (D : D7), Inp D → ∀ (S : Finset ℕ) (dl : ℕ → ℝ), Letters D S dl → ∀ (cc : Ideal (𝓞 D.host.K)), cc = ⊤ → ∀ (δ t0 : ℂ), Crv D cc δ →
      GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a b : ℕ) (e0 : VC D a b → ℂ), oddE0 D cc δ t0 a b e0 →
      ∀ (Ls : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), SD D Ls → SD D Lt →
      ∀ (l : ℕ) [Fact l.Prime], EqAt D l Ls (stdL D a) → EqAt D l Lt (stdL D b) → ∀ k : ℕ, 0 < k → (l ∣ k → SplitIn D l) →
      ∀ (κ : ℂ) (n g : ℕ) (r : Fin n → Qbar) (s : Fin n → VC D a b), Mod1All κ → (∀ lam : Qbar →+* ℂ_[l], ‖lamC lam κ‖ = 1) →
      (∀ i, k • s i ∈ La D (tor0 D cc δ) Ls Lt) → (∀ i, IsIntegral ℤ ((k : Qbar) ^ g * r i)) →
      ∀ (lam : Qbar →+* ℂ_[l]) (mon : GL3Theta.Idx D a b →₀ ℕ),
        Term.Bd lam ((l : ℝ) ^ ((mon.degree : ℝ) * (dl l + (if l = D.host.d then 1 / 4 else 0) + (padicValNat l k : ℝ)) +
            (g : ℝ) * (padicValNat l k : ℝ)))
          (GL3Theta.applyAt0 D (MvPolynomial.monomial mon 1) fun z => κ * ∑ i, (r i : ℂ) *
            U D (tor0 D cc δ) (s i) (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) := by
  intro D hI S dl hL cc hcc δ t0 hC ht a b e0 he0 Ls Lt hLs hLt l _ hEs hEt k hk hsp κ n g r s hκ hκ1 hs hr lam mon
  have hp : l.Prime := Fact.out
  have hp0 : (0 : ℝ) < l := by exact_mod_cast hp.pos
  obtain ⟨β, M, hβ, hloc, hM, hMl, hcmb⟩ :=
    UpperTheory.WildA.cmbIop D hI cc hcc δ t0 hC ht a b e0 he0 Ls Lt hLs hLt l lam hEs hEt k hk
  have hv : padicValNat l (M * k) = padicValNat l k := by
    have hz : padicValNat l M = 0 := by
      simpa only [← Nat.padicValNat_def] using
        (multiplicity_eq_zero_of_not_dvd (hp.coprime_iff_not_dvd.1 hMl.symm))
    rw [(show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hM.ne' hk.ne',
      hz, zero_add]
  have hsp' : l ∣ M * k → SplitIn D l := fun h => hsp (hMl.symm.dvd_of_dvd_mul_left h)
  have hkn := Term.norm_natCast_inv l hk.ne'
  have hk0 : 0 < ‖(k : ℂ_[l])‖ := norm_pos_iff.2 (by exact_mod_cast hk.ne')
  have hrb : ∀ i, KernelAt.Bd lam ((l : ℝ) ^ ((g : ℝ) * (padicValNat l k : ℝ))) (r i : ℂ) := by
    intro i
    refine ⟨(r i).2, ?_⟩
    have h1 : ‖lam ((k : Qbar) ^ g * r i)‖ ≤ 1 := KernelAt.norm_le_one_of_isIntegral (by
      convert map_isIntegral_int lam (hr i) <;> exact Subsingleton.elim _ _)
    rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow] at h1
    rw [mul_comm, Real.rpow_mul_natCast hp0.le, ← hkn, inv_pow, ← one_div, le_div_iff₀ (pow_pos hk0 g), mul_comm]
    exact h1
  have hκb : KernelAt.Bd lam 1 κ := by
    obtain ⟨h, -⟩ := hκ
    refine ⟨h, ?_⟩
    have h1 := hκ1 lam
    rw [lamC, dite_eq_left h] at h1
    exact h1.le
  have hall := KernelAt.Cmb.smul hκb
    (KernelAt.Cmb.sum fun i => KernelAt.Cmb.smul (hrb i) (hcmb (s i) (hs i)))
  have h := UpperTheory.WildA.cmbJet D hI S dl hL cc hcc δ t0 hC ht a b _ l lam β hβ hloc (M * k)
    (Nat.mul_pos hM hk) hsp' _ (by positivity) _ hall mon
  rw [hv, one_mul, mul_one, ← Real.rpow_add hp0, add_comm] at h
  exact h
end
end

-- Source module: Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.KerStd

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.kerStd :
    ∀ (D : D7) (large₂ : SizeData₂ D) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ (ch : Choice R), GlobalTheory.NormSum.Inp D → DictAt ch → ∀ (S : Finset ℕ) (δ : ℕ → ℝ), GlobalTheory.NormSum.Letters D S δ →
      ∀ (t : T) (p : GlobalTheory.ChiGrid.Pair T), DefPair D.R.m p → ∀ (k : ℕ) (d : FinDatum ch.G t p), 0 < k → IsCosetDatum k d → d.z = 1 →
      d.P = locPl ch.G t → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big), ch.S.Z.IsRatAt d x y →
      ∀ (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → (l ∣ k → GlobalTheory.NormSum.SplitIn D l) →
      Formalism.MainNotions.TaylorLogMetric.EqAt D l (latAt ch.S.toGridChoice p.small x) (Formalism.MainNotions.StandardLatticesGL3.stdL D _) →
      Formalism.MainNotions.TaylorLogMetric.EqAt D l (latAt ch.S.toGridChoice p.big y) (Formalism.MainNotions.StandardLatticesGL3.stdL D _) → ∀ (b : ℝ) i j,
        LossLe w ((bVV ℂ (wt ch.G p.big)).repr (ch.S.Z.kkMap 1 d x y (bVV ℂ (wt ch.G p.small) j)) i)
          ((vw w ((l : ℕ) : D.what₂.LL) : ℝ) * GlobalTheory.SumSize.TopInt.kerLoss ch.G δ 1 b p.small p.big l (padicValNat l k)) := by
  intro D large₂ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hI hD S δ hL t p hp k d hk hc hz hP x y hR w l hl hw hsp hx hy b i j
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨Ls, Lt, κ, n, r, s, hLs, hLt, hκ, hs, hr, -, hq, htab⟩ := hD t p hp k d hk hc hz hP x y
  obtain ⟨hEs, hEt, hκ1⟩ := hq l hx hy
  have hcc : D.host.ccK = ⊤ := hS.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hkk := UpperTheory.WildA.kkTab ch.S.Z hp d x y _ htab
  obtain ⟨c, hcJ⟩ := UpperTheory.WildA.jetInt _ _ _ (wtOK_of_defPair ch.G p hp).2 j i
  have hB := UpperTheory.WildA.tabBd D hI S δ hL D.host.ccK hcc ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.4 _ _ (ch.S.Z.e0 p)
    (ch.S.Z.e0_is p hp) Ls Lt hLs hLt l hEs hEt k hk hsp κ n _ r s hκ hκ1 hs hr
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl.one_le
  have hopp : ∀ (z : ℂ) (C : ℝ), (∀ lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[l], GlobalTheory.NormSum.Term.Bd lam C z) →
      ∀ lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[l], GlobalTheory.NormSum.Term.Bd lam C (opp p z) := by
    intro z C h lam
    have hcj : GlobalTheory.NormSum.Term.Bd lam C ((starRingEnd ℂ) z) :=
      ⟨(GlobalTheory.NormSum.conjQbar ⟨z, (h lam).1⟩).2, GlobalTheory.NormSum.conj_bound (h lam).1 (fun lam => (h lam).2) lam⟩
    cases p
    all_goals first | exact h lam | exact hcj
  have hrk : ((ch.G.pS p).rank : ℝ) * (ch.G.pT p).rank = ((ch.G.V p.small).rank : ℝ) * (ch.G.V p.big).rank := by
    cases p
    all_goals first | rfl | exact mul_comm _ _
  refine UpperTheory.WildA.bdLoss D w l hw _ _ ?_ fun lam => ?_
  · have := hR i j
    rwa [Normal.kkIn, LinearMap.toMatrix_apply] at this
  · rw [hkk, hcJ, Finsupp.sum]
    refine GlobalTheory.NormSum.Term.Bd.sum (by positivity) _ _ fun m _ => ?_
    rw [← one_mul ((l : ℝ) ^ _)]
    refine (GlobalTheory.NormSum.Term.Bd.intCast _).mul ?_
    split_ifs with hm
    · refine (hopp _ _ (fun lam => hB lam _) lam).mono (Real.rpow_le_rpow_of_exponent_le hl1 ?_)
      rw [Finsupp.degree_mapDomain, hm]
      unfold GlobalTheory.SumSize.TopInt.kerLoss
      have h0 := hL.2.1 l
      have h2 : 0 ≤ (if (l : ℝ) ≤ 1 * b then Real.logb l (1 * b) else 0) := by
        split_ifs with h
        · exact Real.logb_nonneg (by exact_mod_cast hl.one_lt) (hl1.trans h)
        · exact le_rfl
      have h3 : (0 : ℝ) ≤ (if l = D.host.d then 1 else 0) := by split_ifs <;> norm_num
      have h4 : (if l = D.host.d then (1 : ℝ) / 4 else 0) ≤ (if l = D.host.d then 1 else 0) := by split_ifs <;> norm_num
      have h5 : ((D.R.f * (ch.G.pS p).rank * (ch.G.pT p).rank : ℕ) : ℝ) =
          (D.R.f : ℝ) * (ch.G.V p.small).rank * (ch.G.V p.big).rank := by
        push_cast
        rw [mul_assoc, mul_assoc, hrk]
      rw [h5, add_mul]
      refine le_add_of_le_of_nonneg (add_le_add ?_ ?_) (by positivity)
      · exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      · exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    · exact GlobalTheory.NormSum.Term.Bd.zero (by positivity)
end
end
