module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.AtomEqZero
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.GlCongr
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirProjEqOneOfMem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquiv
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.BlkAtApply
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.QIterSurjective
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.UnipBLeColFixOne
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.QIterSurjective
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.TopMain
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.TwistedKernelFormsNonvanishing
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.UnipBLeColFixOne
import Mathlib.Algebra.Order.Star.Real

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.DerCharBlkAtMirU

section

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mirU_apply {n : ℕ} (u : Mir k n) (hu : mirabolicProjection k n u = 1) (a b : Fin (n + 1))
    (hab : ¬ ((b : ℕ) = n ∧ (a : ℕ) < n)) :
    ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b = if a = b then 1 else 0 := by
  obtain ⟨v, hv⟩ := (GlobalTheory.CompanionTheory.BZMirAdj.mem_of_mirProj_eq_one k n u hu :
    ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hv' : ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v := hv.symm
  rw [hv']
  show (1 + colMat k n v.toAdd) a b = _
  rw [Matrix.add_apply, Matrix.one_apply]
  have hc : colMat k n v.toAdd a b = 0 := by
    simp only [colMat]
    split_ifs with hb
    · have ha0 : ¬ (a : ℕ) < n := fun h' => hab ⟨by rw [hb, Fin.val_last], h'⟩
      have ha : a = Fin.last n := by
        ext
        have := a.isLt
        rw [Fin.val_last]
        omega
      rw [ha, Fin.lastCases_last]
    · rfl
  rw [hc, add_zero]

theorem blkAt_mirU_apply {n N : ℕ} (h : n + 1 ≤ N) (u : Mir k n) (hu : mirabolicProjection k n u = 1) (a b : Fin N)
    (hab : ¬ ((b : ℕ) = n ∧ (a : ℕ) < n)) :
    ((blkAt k (n + 1) N h (u : GL (Fin (n + 1)) k) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) a b =
      if a = b then 1 else 0 := by
  rw [blkAt_apply]
  by_cases ha : (a : ℕ) < n + 1
  · rw [dif_pos ha]
    by_cases hb : (b : ℕ) < n + 1
    · rw [dif_pos hb, mirU_apply u hu _ _ (by simpa using hab)]
      by_cases e : a = b
      · subst e
        simp
      · rw [if_neg e, if_neg]
        intro e'
        exact e (Fin.ext (by simpa using congrArg Fin.val e'))
    · rw [dif_neg hb, if_neg]
      intro e
      subst e
      exact hb ha
  · rw [dif_neg ha]

theorem blkAt_mirU_mem {n N : ℕ} (h : n + 1 ≤ N) (u : Mir k n) (hu : mirabolicProjection k n u = 1) :
    blkAt k (n + 1) N h (u : GL (Fin (n + 1)) k) ∈ derUnip k N n := by
  refine ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩, (GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff _).2 fun i j hj => ?_⟩
  · rw [Fin.lt_def] at hji
    rw [blkAt_mirU_apply h u hu i j (by omega), if_neg (fun e => by rw [e] at hji; omega)]
  · rw [blkAt_mirU_apply h u hu i i (by omega), if_pos rfl]
  · rw [blkAt_mirU_apply h u hu i j (by omega), Matrix.one_apply]

theorem derChar_blkAt_mirU (ψ : AddChar k Circle) {n N : ℕ} (h : n + 1 ≤ N) (u : Mir k n)
    (hu : mirabolicProjection k n u = 1) : derChar k ψ N n ⟨_, blkAt_mirU_mem h u hu⟩ = 1 := by
  rw [derChar_def]
  simp only [whitCharFrom, MonoidHom.coe_comp, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply]
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
  intro p hp
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
  show ((blkAt k (n + 1) N h (u : GL (Fin (n + 1)) k) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p.1 p.2 = 0
  rw [blkAt_mirU_apply h u hu _ _ (by omega), if_neg (fun e => by rw [e] at h1; omega)]

theorem blkAt_levi {n N : ℕ} (h : n + 1 ≤ N) (g : GL (Fin n) k) :
    blkAt k (n + 1) N h ((levi k n g : Mir k n) : GL (Fin (n + 1)) k) = blkAt k n N (by omega) g := by
  ext a b
  rw [blkAt_apply, blkAt_apply]
  have hl : ∀ (a' b' : Fin (n + 1)), (((levi k n g : Mir k n) : GL (Fin (n + 1)) k) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) k) a' b' = glEmbMat k n (g : Matrix (Fin n) (Fin n) k) a' b' :=
    fun _ _ => rfl
  by_cases ha : (a : ℕ) < n
  · have ha' : (a : ℕ) < n + 1 := by omega
    rw [dif_pos ha', dif_pos ha]
    by_cases hb : (b : ℕ) < n
    · have hb' : (b : ℕ) < n + 1 := by omega
      rw [dif_pos hb', dif_pos hb, hl, glEmbMat_apply']
      simp only [ha, hb, dif_pos]
    · rw [dif_neg hb]
      by_cases hb' : (b : ℕ) < n + 1
      · rw [dif_pos hb', hl, glEmbMat_apply']
        simp only [ha, hb, dif_pos, dif_neg, not_false_eq_true]
      · rw [dif_neg hb']
  · rw [dif_neg ha]
    by_cases ha' : (a : ℕ) < n + 1
    · rw [dif_pos ha']
      by_cases hb' : (b : ℕ) < n + 1
      · rw [dif_pos hb', hl, glEmbMat_apply']
        simp only [ha, dif_neg, not_false_eq_true]
        simp only [Fin.ext_iff]
      · rw [dif_neg hb']
        split_ifs with e <;> first | rfl | (simp only [Fin.ext_iff] at e; omega)
    · rw [dif_neg ha']

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_mir {n : ℕ} (p : Mir k n) :
    Matrix.GeneralLinearGroup.det (p : GL (Fin (n + 1)) k) = Matrix.GeneralLinearGroup.det (mirabolicProjection k n p) := by
  have hl := (mem_Mir_iff k (p : GL (Fin (n + 1)) k)).1 p.2
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.det_succ_row _ (Fin.last n), Finset.sum_eq_single (Fin.last n)]
  · rw [hl, Fin.succAbove_last]
    simp only [eLast, Pi.single_eq_same, mul_one, Fin.val_last]
    rw [Even.neg_one_pow ⟨n, rfl⟩, one_mul]
    rfl
  · intro j _ hj
    rw [hl, eLast, Pi.single_eq_of_ne hj]
    simp
  · simp

theorem mir_act (ψ : AddChar k Circle) {n N : ℕ} (h : n + 1 ≤ N) {V D : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup D] [Module ℂ D] (π : Representation ℂ (GL (Fin N) k) V) (ρ' : Representation ℂ (GL (Fin n) k) D)
    (q : V →ₗ[ℂ] D) (hq1 : ∀ g v, q (π (blkAt k n N (by omega) g) v) = ρ' g (q v))
    (hq2 : twKer π (derUnip k N n) (derChar k ψ N n) ≤ LinearMap.ker q) (p : Mir k n) :
    (∀ v, q (π (blkAt k (n + 1) N h p) v) = ρ' (mirabolicProjection k n p) (q v)) ∧
      Matrix.GeneralLinearGroup.det (p : GL (Fin (n + 1)) k) = Matrix.GeneralLinearGroup.det (mirabolicProjection k n p) := by
  have hu1 : mirabolicProjection k n (p * (levi k n (mirabolicProjection k n p))⁻¹) = 1 := by
    rw [map_mul, map_inv, GlobalTheory.CompanionTheory.BZMirAdj.mirProj_levi, mul_inv_cancel]
  have hp : (p : GL (Fin (n + 1)) k) = ((p * (levi k n (mirabolicProjection k n p))⁻¹ : Mir k n) : GL (Fin (n + 1)) k) *
      ((levi k n (mirabolicProjection k n p) : Mir k n) : GL (Fin (n + 1)) k) := by
    rw [← Subgroup.coe_mul, inv_mul_cancel_right]
  have hkill : ∀ w, q (π (blkAt k (n + 1) N h
      ((p * (levi k n (mirabolicProjection k n p))⁻¹ : Mir k n) : GL (Fin (n + 1)) k)) w) = q w := by
    intro w
    rw [← sub_eq_zero, ← map_sub]
    apply hq2
    refine Submodule.subset_span ⟨⟨_, blkAt_mirU_mem h _ hu1⟩, w, ?_⟩
    rw [derChar_blkAt_mirU ψ h _ hu1]
    simp
  refine ⟨fun v => ?_, det_mir p⟩
  conv_lhs => rw [hp]
  rw [map_mul, map_mul, Module.End.mul_apply, hkill, blkAt_levi, hq1]

end PositivityTheory.RgUd.Form.U.Asm
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.NabsDetScalar

section

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.LocGL GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U PositivityTheory.RgUd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem gLEq_congr {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}
    {a b : ℕ} (hab : a = b) {ha : a + 1 ≤ N} {hb : b + 1 ≤ N} {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
    (h : GLEq k π a ha s B) : GLEq k π b hb s B := by
  subst hab; exact h

theorem isAtom_congr {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}
    {a b : ℕ} (hab : a = b) {ha : a + 2 ≤ N} {hb : b + 2 ≤ N} {B B₀ : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
    (h : IsAtom ha π B B₀) : IsAtom hb π B B₀ := by
  subst hab; exact h

theorem scalAt_eq (n N : ℕ) (h : n ≤ N) (z : kˣ) :
    scalAt k n N h z = blkAt k n N h (GeneralLinearGroup.scalar (Fin n) z) := by
  unfold scalAt
  congr 1

theorem nabs_det_scalar (n : ℕ) (z : kˣ) :
    nabs k (GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin n) z)) = nabs k z ^ n := by
  rw [GeneralLinearGroup.det_scalar, Fintype.card_fin]
  simp [nabs, map_pow]

theorem derivTop_of (hUA : UAtom k) (hUD : UDens k) (hUS : USplit k) (hUL : ULift k) (hUAd : UAdm k)
    (hTB : ThmB k) : DerivTop k := by
  intro ψ hψc hψ1 n h π hh1 hsm hirr hunit hnt hsub
  obtain ⟨j, rfl⟩ : ∃ j, h = j + 1 := ⟨h - 1, by omega⟩
  obtain ⟨B, hBh, hBp, hBi⟩ := hunit
  have hB : IsInvForm π.ρ B := ⟨hBh, hBp, hBi⟩
  obtain ⟨q, hqs, hqk, hqe⟩ := derDict ψ n j π.ρ
  have hvan : ∀ n', n' < n → twKer π.ρ (derUnip k (n + (j + 1)) n') (derChar k ψ (n + (j + 1)) n') = ⊤ := by
    intro n' hn'
    have e : n + (j + 1) = n' + ((n + j - n') + 1) := by omega
    exact (cast_twKer ψ e π n').1 ((sub_iff_twKer ψ n' (n + j - n') (π.cast e)).1 (hsub n' _ e (by omega)))
  have hE1 : IsPsd (chain hUD hψc hψ1 π.ρ hsm B j) := chain_psd hUD hψc hψ1 π.ρ hsm B hB j (by omega)
  have hker : twKer π.ρ (derUnip k (n + (j + 1)) (n + (j + 1) - j)) (lvlChar k ψ (n + (j + 1)) (n + (j + 1) - j)) ≤
      LinearMap.ker q := by
    rw [hqk, lvlChar_def, derChar_def]
    exact twKer_derUnip_le ψ π.ρ (a := n + (j + 1) - j) (b := n) (x := n + (j + 1) - j - 1) (y := n)
      (by omega) (by omega) (by omega)
  have hE3 : ∀ v, chain hUD hψc hψ1 π.ρ hsm B j v v = 0 → v ∈ LinearMap.ker q :=
    fun v hv => hker (chain_rad hUD hψc hψ1 π.ρ hsm B hB j (by omega) v hv)
  have hq2 : twKer π.ρ (derUnip k (n + (j + 1)) n) (derChar k ψ (n + (j + 1)) n) ≤ LinearMap.ker q := by
    rw [hqk]
    exact le_rfl

  have hE24 : (∀ v ∈ LinearMap.ker q, ∀ w, chain hUD hψc hψ1 π.ρ hsm B j v w = 0) ∧
      ∀ (g : GL (Fin n) k) v w, chain hUD hψc hψ1 π.ρ hsm B j (π.ρ (blkAt k n (n + (j + 1)) (by omega) g) v)
        (π.ρ (blkAt k n (n + (j + 1)) (by omega) g) w) =
        ((nabs k (GeneralLinearGroup.det g) ^ (j : ℝ) : ℝ) : ℂ) * chain hUD hψc hψ1 π.ρ hsm B j v w := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      refine ⟨fun v hv w => ?_, fun g v w => ?_⟩
      · have hK := chain_kills hUD hψc hψ1 π.ρ hsm B hB j (by omega)
        have e1 : 0 + (j + 1) - j = 1 := by omega
        rw [e1] at hK
        refine hK v ?_ w
        have hle : twKer π.ρ (derUnip k (0 + (j + 1)) 0) (derChar k ψ (0 + (j + 1)) 0) ≤
            twKer π.ρ (derUnip k (0 + (j + 1)) 1) (lvlChar k ψ (0 + (j + 1)) 1) :=
          twKer_mono π.ρ _ _ (le_inf inf_le_left (inf_le_left.trans (unipB_le_colFix_one _))) fun u => rfl
        rw [hqk] at hv
        exact hle hv
      · have hg : g = 1 := by
          ext i
          exact Fin.elim0 i
        subst hg
        simp [nabs]
    · obtain ⟨n₀, rfl⟩ : ∃ n₀, n = n₀ + 1 := ⟨n - 1, by omega⟩
      have hN2 : j + 2 ≤ n₀ + 1 + (j + 1) := by omega
      have h0 : ∀ v, chain hUD hψc hψ1 π.ρ hsm B (j + 1) v v = 0 := by
        by_contra hc
        push_neg at hc
        obtain ⟨n', hn', hne⟩ := twisted_kernel_forms_nonvanishing hUD hUA hψc hψ1 π.ρ hsm B hUS hB n₀ (j + 1) (by omega) hc
        exact hne (hvan n' (by omega))
      have hA := atom_eq_self hUD hUA hψc hψ1 π.ρ hsm B hUS hB j hN2 h0
      obtain ⟨-, -, -, hK, hG, -⟩ := atom_spec hUD hUA hψc hψ1 π.ρ hsm B j hN2
        (chain_lvl hUD hψc hψ1 π.ρ hsm B hB j hN2)
      rw [hA] at hK hG
      refine ⟨fun v hv w => ?_, fun g v w => ?_⟩
      · unfold DerKer at hK
        have e2 : n₀ + 1 + (j + 1) - 2 - j + 1 = n₀ + 1 := by omega
        rw [e2] at hK
        rw [hqk] at hv
        exact hK v hv w
      · have hG' : GLEq k π.ρ n₀ (by omega) (j : ℝ) (chain hUD hψc hψ1 π.ρ hsm B j) := gLEq_congr (by omega) hG
        exact hG' g v w
  obtain ⟨hE2, hE4⟩ := hE24
  refine top_core (by omega : n ≤ n + (j + 1)) π.ρ (derivB ψ (j + 1) π).ρ
    (hUAd ψ hψc hψ1 n (j + 1) π hsm hirr) q hqs hqe (j : ℝ) ((1 - ((j + 1 : ℕ) : ℝ)) / 2) (by push_cast; ring)
    (chain hUD hψc hψ1 π.ρ hsm B j) hE1 hE2 hE3 hE4 ?_
  intro C hC1 hC2 hC3 hC4
  refine lift hUD hψc hψ1 π.ρ hsm B hUL hTB hirr hB j (by omega) C hC1 (fun v hv w => hC2 v (hker hv) w) ?_ hC4
  refine mirEq_congr (a := n) (ha := by omega) (by omega) rfl ?_
  intro p hp v w
  obtain ⟨hact, hdet⟩ := mir_act ψ (by omega : n + 1 ≤ n + (j + 1)) π.ρ (derivB ψ (j + 1) π).ρ q hqe hq2 ⟨p, hp⟩
  have e : C (π.ρ (blkAt k (n + 1) (n + (j + 1)) (by omega) p) v) (π.ρ (blkAt k (n + 1) (n + (j + 1)) (by omega) p) w) =
      C (π.ρ (blkAt k n (n + (j + 1)) (by omega) (mirabolicProjection k n ⟨p, hp⟩)) v)
        (π.ρ (blkAt k n (n + (j + 1)) (by omega) (mirabolicProjection k n ⟨p, hp⟩)) w) :=
    factor hC1.1 q hC2 ((hact v).trans (hqe _ v).symm) ((hact w).trans (hqe _ w).symm)
  rw [e, hC3, ← hdet]



theorem derivPos_of (hUA : UAtom k) (hUD : UDens k) (hUS : USplit k) (hUL : ULift k) (hUSh : UShell k)
    (hUE : UEig k) (hTB : ThmB k) : DerivPos k := by
  intro ψ hψc hψ1 n i π hi hsm hirr hunit hex W _ _ σ ω hW hsq hcc z hz
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  obtain ⟨B, hBh, hBp, hBi⟩ := hunit
  have hB : IsInvForm π.ρ B := ⟨hBh, hBp, hBi⟩
  obtain ⟨n', h', e, hlt, hnt'⟩ := hex
  obtain ⟨j', rfl⟩ : ∃ j', h' = j' + 1 := ⟨h' - 1, by omega⟩
  have hne : twKer π.ρ (derUnip k (n + (j + 1)) n') (derChar k ψ (n + (j + 1)) n') ≠ ⊤ := by
    intro htop
    have h2 := (sub_iff_twKer ψ n' j' (π.cast e)).2 ((cast_twKer ψ e π n').2 htop)
    exact not_subsingleton _ h2
  obtain ⟨n₀, rfl⟩ : ∃ n₀, n = n₀ + 1 := ⟨n - 1, by omega⟩
  set t : ℝ := (1 - ((j + 1 : ℕ) : ℝ)) / 2 with ht
  obtain ⟨x, hx0, hxe⟩ := hUE ψ hψc hψ1 (n₀ + 1) (j + 1) π hsm hirr t W σ ω hW hsq hcc z
  obtain ⟨q, hqs, hqk, hqe⟩ := derDict ψ (n₀ + 1) j π.ρ
  obtain ⟨v, rfl⟩ := hqs x
  set g := GeneralLinearGroup.scalar (Fin (n₀ + 1)) z with hg
  set ct : ℂ := ((dpow (n₀ + 1) t g : ℂˣ) : ℂ) with hct
  have hct0 : ct ≠ 0 := Units.ne_zero _
  set c : ℂ := ct⁻¹ * (ω z : ℂ) with hc
  have hx0' : q v ≠ (0 : TwJacquet (iterPhi k ψ j (resM k π.ρ)).ρ (MirUin k (n₀ + 1)) 1) := hx0
  have hρ : GlobalTheory.BZMir.deriv k ψ j π.ρ g (q v) = c • q v := by
    have h1 : ct • GlobalTheory.BZMir.deriv k ψ j π.ρ g (q v) = (ω z : ℂ) • q v := hxe
    calc GlobalTheory.BZMir.deriv k ψ j π.ρ g (q v) = ct⁻¹ • (ct • GlobalTheory.BZMir.deriv k ψ j π.ρ g (q v)) := by
          rw [smul_smul, inv_mul_cancel₀ hct0, one_smul]
      _ = c • q v := by rw [h1, smul_smul]
  have hN2 : j + 2 ≤ n₀ + 1 + (j + 1) := by omega

  have hchne := chain_ne_of hUD hψc hψ1 π.ρ hsm B hB (j + 1) n' (by omega) (by omega) hne
  have hA0 := atom_eq_zero hUD hUA hψc hψ1 π.ρ hsm B hUS hUL hTB hirr hB j hN2 hchne
  have hAz : atom hUD hUA hψc hψ1 π.ρ hsm B j = 0 := by
    ext a b
    simp [hA0 a b]
  have hL := chain_lvl hUD hψc hψ1 π.ρ hsm B hB j hN2
  obtain ⟨hAt, -⟩ := atom_spec hUD hUA hψc hψ1 π.ρ hsm B j hN2 hL
  rw [hAz] at hAt
  have hL' : Lvl k ψ π.ρ n₀ (by omega) (j : ℝ) (chain hUD hψc hψ1 π.ρ hsm B j) := lvl_congr (by omega) rfl hL
  have hAt' : IsAtom (by omega : n₀ + 2 ≤ n₀ + 1 + (j + 1)) π.ρ (chain hUD hψc hψ1 π.ρ hsm B j) 0 :=
    isAtom_congr (by omega) hAt
  have hmem : π.ρ (scalAt k (n₀ + 1) (n₀ + 1 + (j + 1)) (by omega) z) v - c • v ∈ DerKer k ψ π.ρ n₀ := by
    have : π.ρ (scalAt k (n₀ + 1) (n₀ + 1 + (j + 1)) (by omega) z) v - c • v ∈ LinearMap.ker q := by
      rw [LinearMap.mem_ker, map_sub, map_smul, scalAt_eq]
      have h2 : q (π.ρ (blkAt k (n₀ + 1) (n₀ + 1 + (j + 1)) (by omega) g) v) = GlobalTheory.BZMir.deriv k ψ j π.ρ g (q v) :=
        hqe g v
      rw [h2, hρ, sub_self]
    rw [hqk] at this
    exact this
  have hnot : v ∉ DerKer k ψ π.ρ n₀ ⊔ LinearMap.ker (chain hUD hψc hψ1 π.ρ hsm B j) := by
    intro hv
    have hle : LinearMap.ker (chain hUD hψc hψ1 π.ρ hsm B j) ≤ DerKer k ψ π.ρ n₀ := by
      intro a ha
      have ha0 : chain hUD hψc hψ1 π.ρ hsm B j a a = 0 := by
        rw [LinearMap.mem_ker] at ha
        rw [ha]
        rfl
      have hr := chain_rad hUD hψc hψ1 π.ρ hsm B hB j (by omega) a ha0
      rw [lvlChar_def] at hr
      unfold DerKer
      rw [derChar_def]
      exact twKer_derUnip_le ψ π.ρ (a := n₀ + 1 + (j + 1) - j) (b := n₀ + 1) (x := n₀ + 1 + (j + 1) - j - 1)
        (y := n₀ + 1) (by omega) (by omega) (by omega) hr
    have hv' : v ∈ LinearMap.ker q := by
      rw [hqk]
      exact (sup_le le_rfl hle) hv
    exact hx0' (LinearMap.mem_ker.1 hv')
  have hsh := hUSh ψ hψc hψ1 n₀ (n₀ + 1 + (j + 1)) (by omega) π.V π.ρ hsm (j : ℝ)
    (chain hUD hψc hψ1 π.ρ hsm B j) hL' hAt' z c v hz hmem hnot

  have ha := nabs_pos k z
  set a := nabs k z with ha_def
  have hctv : ct = (((a ^ (n₀ + 1) : ℝ) ^ t : ℝ) : ℂ) := by
    rw [hct, dpow_val, hg, nabs_det_scalar]
  have hω : (ω z : ℂ) = c * ct := by
    rw [hc, mul_comm, ← mul_assoc, mul_inv_cancel₀ hct0, one_mul]
  have hnct : ‖ct‖ ^ 2 = a ^ (-(((n₀ : ℝ) + 1) * j)) := by
    rw [hctv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), ← Real.rpow_natCast a (n₀ + 1),
      ← Real.rpow_mul ha.le, ← Real.rpow_natCast _ 2, ← Real.rpow_mul ha.le, ht]
    congr 1
    push_cast
    ring
  have hprod : ‖(ω z : ℂ)‖ ^ 2 < 1 := by
    rw [hω, norm_mul, mul_pow, hnct]
    have hpos : 0 < a ^ (-(((n₀ : ℝ) + 1) * j)) := Real.rpow_pos_of_pos ha _
    calc ‖c‖ ^ 2 * a ^ (-(((n₀ : ℝ) + 1) * j)) < a ^ (((n₀ : ℝ) + 1) * j) * a ^ (-(((n₀ : ℝ) + 1) * j)) :=
          mul_lt_mul_of_pos_right hsh hpos
      _ = 1 := by rw [← Real.rpow_add ha, add_neg_cancel, Real.rpow_zero]
  nlinarith [norm_nonneg (ω z : ℂ)]

theorem uAsm : UAsm k := fun hUA hUD hUS hUL hUSh hUE hUAd hTB =>
  ⟨derivTop_of hUA hUD hUS hUL hUAd hTB, derivPos_of hUA hUD hUS hUL hUSh hUE hTB⟩

end PositivityTheory.RgUd.Form.U.Asm
end
end
end
