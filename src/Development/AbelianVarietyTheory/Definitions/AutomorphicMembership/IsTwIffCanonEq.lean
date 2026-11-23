module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.Columns.ChainTwOk
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalFractionsRepresentPrimeNormQuotient
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemVGsOfMemQE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharLocalEqInvTypeCharacter
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Formalism.LocalToGlobal.Columns.ColFormsLemmas
public import Formalism.LocalToGlobal.Columns.DGamAut
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Formalism.LocalToGlobal.Columns.ChainInstY
public import Formalism.LocalToGlobal.Columns.ChainTwCst
public import Formalism.LocalToGlobal.Columns.ChainTwFin
public import Formalism.LocalToGlobal.Columns.ThetaOpenTwLevQ
public import Formalism.LocalToGlobal.Columns.UnfoldingNonvanishingDoubleCosetHolds
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Formalism.LocalToGlobal.Columns.ChainFrmOk

section

@[expose] public section

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem frm_exists_c (p p0 : DecoF X.E n ST SG Q) (h : p.deco = p0.deco) :
    ∃ c : GLQ X.E n Q, p = ((1, 1, c) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • p0 := by
  refine ⟨fun P => ⟨(p.fr P)⁻¹ * p0.fr P, ?_⟩, ?_⟩
  · show ∀ x, ((p.fr P)⁻¹ * p0.fr P) x ∈ stdAt X.E n P.1 ↔ x ∈ stdAt X.E n P.1
    intro x
    have hx : p.1.2 P (((p.fr P)⁻¹ * p0.fr P) x) = p0.1.2 P x := LinearEquiv.apply_symm_apply _ _
    have h' : p.1.1 = p0.1.1 := h
    rw [← p.2 P, hx, h', p0.2 P]
  · apply Subtype.ext
    simp only [HSMul.hSMul, SMul.smul]
    refine Prod.ext ?_ ?_
    · have h1 := one_smul (UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) p0.1.1
      simp only [HSMul.hSMul, SMul.smul] at h1
      exact h.trans h1.symm
    · funext P
      simp only [DecoF.fr, OneMemClass.coe_one, one_mul, InvMemClass.coe_inv, _root_.mul_inv_rev, inv_inv,
        ← mul_assoc, mul_inv_cancel]

variable (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q)

theorem frm_root (hroot : ∀ c : ↥Θ.grp, ∃ m : ℕ, 0 < m ∧ ((Θ.chr c : X.Kˣ) : X.K) ^ m = 1) (g : FrmG Λ Θ) :
    ∃ m : ℕ, 0 < m ∧ (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) ^ m = 1 := by
  haveI : ∀ w : SG, Finite (𝓞 X.E ⧸ w.1.asIdeal) := fun w =>
    Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
  obtain ⟨m2, hm2, h2⟩ := hroot g.2.2
  have hfo : IsOfFinOrder g.2.1 := isOfFinOrder_of_finite _
  have ha : ((Λ.chr g.2.1 : X.Kˣ) : X.K) ^ orderOf g.2.1 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  refine ⟨orderOf g.2.1 * m2, Nat.mul_pos hfo.orderOf_pos hm2, ?_⟩
  rw [Units.val_mul, mul_pow, pow_mul, ha, one_pow, one_mul, mul_comm (orderOf _) m2, pow_mul, h2,
    one_pow]


open Classical in
theorem frmGSD_ok_of_finIdx (hX : X.Ok) (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (hC : C.Eqv)
    (hfi : ∀ P : Q, Finite (↥(GLint X.E n P.1) ⧸ (Θ P).H))
    (hroot : ∀ c : ↥Θ.grp, ∃ m : ℕ, 0 < m ∧ ((Θ.chr c : X.Kˣ) : X.K) ^ m = 1) : (frmGSD (C.pull DecoF.deco) Λ Θ).Ok := by
  refine { fin_orb := ?_, fin_stab := ?_, nab_smul := ?_, del_smul := ?_, inv := ?_ }
  · obtain ⟨s, hs, hrep⟩ := DecoSet.finite_reps (ST := ST) (SG := SG) (n := n) (posStar_of_conj hX.conjE)
    have : Finite s := hs

    let pt : s → (∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H) → Option (DecoF X.E n ST SG Q) := fun d cb =>
      if h : ∃ p0 : DecoF X.E n ST SG Q, p0.deco = d.1 then
        some (((1, 1, fun P => ((cb P).out)⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • h.choose) else none
    have hfin : Finite (Option (s × (∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H))) := inferInstance
    by_cases hne : Nonempty (frmGSD (C.pull DecoF.deco) Λ Θ).Cl
    swap
    · have := not_nonempty_iff.1 hne
      exact inferInstance
    obtain ⟨c00⟩ := hne
    refine Finite.of_surjective (fun a : s × (∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H) =>
      match pt a.1 a.2 with
      | some p => (frmGSD (C.pull DecoF.deco) Λ Θ).cls p
      | none => c00) ?_
    intro c
    induction c using Quotient.inductionOn' with
    | h p =>
      obtain ⟨d0, hd0, g, hg⟩ := hrep (DecoF.deco p)

      let p1 : DecoF X.E n ST SG Q := ((g, 1, 1) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q)⁻¹ • p
      have hp1 : p1.deco = d0 := by
        show ((g, (1 : GLG (E := X.E) (n := n) (SG := SG))) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG))⁻¹ • p.deco = d0
        rw [hg, inv_smul_smul]
      have hex : ∃ p0 : DecoF X.E n ST SG Q, p0.deco = d0 := ⟨p1, hp1⟩
      obtain ⟨c, hc⟩ := frm_exists_c p1 hex.choose (hp1.trans hex.choose_spec.symm)

      let cb : ∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H := fun P => QuotientGroup.mk ((c P)⁻¹)
      have hout : ∀ P : Q, ((c P)⁻¹)⁻¹ * (cb P).out ∈ (Θ P).H := fun P => QuotientGroup.eq.1 (QuotientGroup.out_eq' (cb P)).symm
      refine ⟨(⟨d0, hd0⟩, cb), ?_⟩
      have hpt : pt ⟨d0, hd0⟩ cb = some (((1, 1, fun P => ((cb P).out)⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • hex.choose) := dif_pos hex
      show (match pt ⟨d0, hd0⟩ cb with
        | some p => (frmGSD (C.pull DecoF.deco) Λ Θ).cls p
        | none => c00) = _
      rw [hpt]
      let θ : ↥Θ.grp := ⟨fun P => ((c P)⁻¹)⁻¹ * (cb P).out, fun P _ => hout P⟩
      refine ((frmGSD (C.pull DecoF.deco) Λ Θ).cls_eq_iff _ p).mpr ⟨((g, 1, θ) : FrmG Λ Θ)⁻¹, ?_⟩
      refine inv_smul_eq_iff.2 (Eq.symm ?_)
      show ((g, (1 : GLG (E := X.E) (n := n) (SG := SG)), (θ : GLQ X.E n Q)) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) •
        (((1, 1, fun P => ((cb P).out)⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • hex.choose) = p
      rw [← mul_smul]
      have e : ((g, (1 : GLG (E := X.E) (n := n) (SG := SG)), (θ : GLQ X.E n Q)) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) * (1, 1, fun P => ((cb P).out)⁻¹) =
          (g, 1, 1) * (1, 1, c) := by
        refine Prod.ext (by simp) (Prod.ext (by simp) ?_)
        funext P
        show ((c P)⁻¹)⁻¹ * (cb P).out * ((cb P).out)⁻¹ = 1 * c P
        group
      rw [e, mul_smul, ← hc]
      exact smul_inv_smul _ p
  · intro p
    have := DecoSet.finite_stabilizer (posStar_of_conj hX.conjE) (DecoF.deco p : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))
    refine Finite.of_injective
      (fun a : MulAction.stabilizer (frmGSD (C.pull DecoF.deco) Λ Θ).G p =>
        (⟨(a.1.1, (a.1.2.1 : GLG (E := X.E) (n := n) (SG := SG))), congrArg DecoF.deco a.2⟩ :
          MulAction.stabilizer (UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) (DecoF.deco p : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)))) ?_
    intro a b hab
    have h0 : ((a.1.1, (a.1.2.1 : GLG (E := X.E) (n := n) (SG := SG))) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) = (b.1.1, (b.1.2.1 : GLG (E := X.E) (n := n) (SG := SG))) :=
      congrArg Subtype.val hab
    exact Subtype.ext (dga_frm_stab_inj Λ Θ p a.2 b.2 (Prod.mk.inj h0).1)
  · intro g d
    obtain ⟨m, hm, hc⟩ := frm_root Λ Θ hroot g
    exact (hC.nab_smul (g.1, (g.2.1 : GLG (E := X.E) (n := n) (SG := SG))) (DecoF.deco d)).trans (map_root_smul _ _ hm hc).symm
  · intro g d
    obtain ⟨m, hm, hc⟩ := frm_root Λ Θ hroot g
    exact (hC.del_smul (g.1, (g.2.1 : GLG (E := X.E) (n := n) (SG := SG))) (DecoF.deco d)).trans (map_root_smul _ _ hm hc).symm
  · intro g (x : C.V) (y : C.V)
    obtain ⟨m, hm, hc⟩ := frm_root Λ Θ hroot g
    show C.pair ((((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) • C.rho g.1 x)
      ((((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) • C.rho g.1 y) = C.pair x y
    rw [LinearMap.map_smulₛₗ₂, map_smul, hC.inv, smul_smul]
    show (star (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) * _) • _ = _
    rw [star_mul_root hX.conjK hm hc, one_smul]

end Gen

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

theorem chF_ok_of_finIdx (hX : X.Ok) (u : Pr.Word) (j : ℕ)
    (hfi : ∀ (b : L.β j) (P : QE sel (mu : Chr X.F X.E X.K)), Finite (↥(GLint X.E (R.N j) P.1) ⧸ (L.levQ j b P).H))
    (hroot : ∀ (b : L.β j) (c : ↥(L.levQ j b).grp), ∃ m : ℕ, 0 < m ∧ (((L.levQ j b).chr c : X.Kˣ) : X.K) ^ m = 1) :
    (chF W sel mu L u j).Ok := by
  intro b
  have hC : (colVal W u j (Pr.vT u) Pr.vGs).Eqv :=
    ⟨colVal_nab_smul W u j, colVal_del_smul W u j, roundPk_inv X _ _ hX.emb_star⟩
  exact frmGSD_ok_of_finIdx (L.levG j b) (L.levQ j b) hX (colVal W u j (Pr.vT u) Pr.vGs)
    hC (hfi b) (hroot b)

end Chain

end Formalism.L2.Col
end
end
end

-- Source module: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def IsTw : Prop := ∀ a, I.cst a = twCst I.Ch I.sel (I.tup a) I.glob ∧
  I.idx a = twIdx I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 2)

@[reducible] def canon : TC B X :=
  { I with
    cst := fun a => twCst I.Ch I.sel (I.tup a) I.glob
    idx := fun a => twIdx I.Ch I.sel (I.tup a) (twCst I.Ch I.sel (I.tup a) I.glob) (B.R.m - 2) }

theorem canon_isTw : I.canon.IsTw := fun _ => ⟨rfl, rfl⟩

def Deep : Prop := ∀ a (P : rowSG (B.primes X) I.sel (I.tup a)), P.1 ∉ (B.primes X).vGs → 2 * B.R.m ≤ (I.cst a).D P

variable {I}

theorem IsTw.cst_eq (h : I.IsTw) (a : I.ι) : I.cst a = twCst I.Ch I.sel (I.tup a) I.glob := (h a).1

theorem IsTw.idx_eq (h : I.IsTw) (a : I.ι) :
    I.idx a = twIdx I.Ch I.sel (I.tup a) (twCst I.Ch I.sel (I.tup a) I.glob) (B.R.m - 2) := by
  rw [(h a).2, (h a).1]

theorem IsTw.deep (h : I.IsTw) : I.Deep := fun a P hP => by
  rw [h.cst_eq a, twCst_D_Q hP]

theorem qOf_mod_four (B : Base) (X : PreX B.toPre) : ∀ w ∈ (B.primes X).vGs, qOf w % 4 = 1 := fun w hw => by
  have hPr := (base_fields_primes_ok B X).2.1
  obtain ⟨k, hk⟩ : ∃ k, w ∈ (B.primes X).vG k := by
    classical
    unfold Primes.vGs at hw
    rcases Finset.mem_union.1 hw with h | h
    exacts [⟨0, h⟩, ⟨1, h⟩]
  rw [show qOf w = (B.primes X).g k from hPr.vG_norm k w hk]
  exact (hPr.g_cong k).of_dvd (by
    show 4 ∣ B.host.QS * B.host.q * B.host.d
    exact (((pow_dvd_pow 2 (Nat.le_add_left 2 B.R.e) : 2 ^ 2 ∣ 2 ^ (B.R.e + 2)).trans B.host.tower_dvd).mul_right _).mul_right _)

theorem val_of_ok (h : I.Ok) (j : Fin B.R.m) (w : HeightOneSpectrum (𝓞 B.fields.E)) (hw : w ∈ (B.primes X).vGs) :
    ∃ y : B.fields.K, I.glob.σ₀ y = ((((I.glob.mu0 j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹ := by
  classical
  have hq : (qOf w : B.fields.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero w
  have e := (h.idx_ok I.mu0).muqG j j.2 ⟨w, Finset.mem_union_left _ hw⟩ hw (ciQU w) (by simp [ciQU, hq])
  refine ⟨(I.cst I.mu0).muq (j + 1) ⟨w, Finset.mem_union_left _ hw⟩ *
    (qValC (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) w : B.fields.Kˣ), ?_⟩
  rw [map_mul, e, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one]

theorem Q_notMem_of_ok (h : I.Ok) (a : I.ι) : ∀ P ∈ I.Q a, P ∉ (B.primes X).vGs := fun _ hP =>
  IdxEx.notMem_vGs_of_mem_QE (base_fields_primes_ok B X).1 (base_fields_primes_ok B X).2.1 h.sel_ok h.g_mem (I.tup a) hP

theorem degOne_of_ok (h : I.Ok) (a : I.ι) (P : rowSG (B.primes X) I.sel (I.tup a)) : TwDegOne B.fields P.1 :=
  degOneUnram_rowSG (base_fields_primes_ok B X).1 (base_fields_primes_ok B X).2.1 h.sel_ok (I.tup a) P

theorem sqrt_of_ok (h : I.Ok) (a : I.ι) (P : rowSG (B.primes X) I.sel (I.tup a)) : ∃ z : B.fields.K, z ^ 2 = (qOf P.1 : B.fields.K) :=
  ⟨_, (h.idx_ok a).cst_ok.sq_sq P⟩

theorem root_of_ok (h : I.Ok) (hD : I.Deep) (a : I.ι) (P : rowSG (B.primes X) I.sel (I.tup a)) (hP : P.1 ∉ (B.primes X).vGs) :
    ∃ z : B.fields.K, I.glob.σ₀ z = Complex.exp (2 * Real.pi * Complex.I / ((qOf P.1 ^ (2 * B.R.m) : ℕ) : ℂ)) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hD a P hP)
  have hq : (qOf P.1 : B.fields.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P.1
  have hqC : (qOf P.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.cast_ne_zero.1 hq)
  obtain ⟨x1, x2⟩ := (h.idx_ok a).xiUnitAtPrime P
  have hx : I.glob.xi0 ≠ 0 := fun e => x2 (e ▸ redP_zero)
  have hi : IntAt P.1 ((qOf P.1 ^ k : ℕ) : B.fields.E) := by
    simpa using GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.intAt_int P.1 ((qOf P.1 ^ k : ℕ) : ℤ)
  have e := (h.idx_ok a).weil P (I.glob.xi0⁻¹ / (qOf P.1 : B.fields.E) ^ (2 * B.R.m)) ((qOf P.1 ^ k : ℕ) : ℤ)
    (by
      convert hi.mul (yIntAt_inv x1 x2) using 1
      rw [hk]; push_cast; field_simp; ring)
    (by
      convert GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.intAt_int P.1 0 using 1
      rw [hk]; push_cast; field_simp; ring)
  refine ⟨_, e.trans ?_⟩
  congr 1
  rw [hk]; push_cast; field_simp; ring

theorem twIdx_ok_of_ok (h : I.Ok) (hD : I.Deep) (a : I.ι) :
    (twIdx I.Ch I.sel (I.tup a) (twCst I.Ch I.sel (I.tup a) I.glob) (B.R.m - 2)).Ok I.Ch I.sel (I.tup a)
      (twCst I.Ch I.sel (I.tup a) I.glob) I.glob (B.R.m - 2) :=
  twIdx_ok_closed (base_fields_primes_ok B X).1 (base_fields_primes_ok B X).2.1 h.ch_ok (qOf_mod_four B X) I.glob
    h.ch_tied h.weil (val_of_ok h) h.hm (Q_notMem_of_ok h a) (fun P _ => degOne_of_ok h a P) (root_of_ok h hD a)
    (fun P _ => sqrt_of_ok h a P) (fun P _ => (h.idx_ok a).xiUnitAtPrime P)

theorem canon_ok (h : I.Ok) (hD : I.Deep) : I.canon.Ok :=
  { h with sharp := fun _ => rfl, idx_ok := twIdx_ok_of_ok (I := I) h hD }

theorem IsTw.chF_ok (ht : I.IsTw) (h : I.Ok) (W : Wts B.fields (B.primes X).Word B.R) (a : I.ι) (u : (B.primes X).Word) (j : ℕ) :
    (chF W I.sel (I.tup a) (I.idx a) u j).Ok := by
  have ho : ∀ b, ThetaOpen ((I.idx a).levQ j b) := by
    rw [(ht a).2]
    exact thetaOpen_twIdx I.Ch I.sel (I.tup a) (I.cst a) (h.idx_ok a).cst_ok (Q_notMem_of_ok h a) _ j
  exact chF_ok_of_finIdx W I.sel (I.tup a) _ (base_fields_primes_ok B X).1 u j
    (fun b P => thetaOpen_finIdx _ (ho b) P) (fun b c => thetaOpen_root _ (ho b) c)

end GlobalTheory.Mem.Col2.TC

end
end
end
