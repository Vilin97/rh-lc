module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DimFormC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KppOffCOfSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelevantSetZeroGNotIdentity
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellFin
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.ClauseAOfIdentityFlag
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdLift
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.UnitriangularFrameLift
public import Mathlib.RingTheory.Ideal.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Order.Star.Int
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdScal
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SplittingAdmissibleOfTermData
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SplittingAdmissibleOfTermData

-- Source module: Lemmata.GeneralBFactUpperVersion.Imports

section

@[expose] public section

namespace Bl.general_b_fact_upper_version

theorem goal1 :
  ∀ {R : Type} [inst : CommRing.{0} R] [IsDomain.{0} R] (ζ : R) (M : Nat) (P : Ideal.{0} R),
  Ne.{1} ζ 1 →
    Eq.{1} (HPow.hPow.{0, 0, 0} ζ M) 1 →
      Membership.mem.{0, 0} P (HSub.hSub.{0, 0, 0} ζ 1) → Membership.mem.{0, 0} P (Nat.cast.{0} M) := by
  intro R _ _ ζ M P h1 hM hP
  have hs : (∑ i ∈ Finset.range M, ζ ^ i) = 0 := by
    have h := geom_sum_mul ζ M
    rw [hM, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr h1)
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hP ⊢
  have h2 : Ideal.Quotient.mk P ζ = 1 := by
    rw [map_sub, map_one, sub_eq_zero] at hP
    exact hP
  have h3 := congrArg (Ideal.Quotient.mk P) hs

  simpa [map_sum, map_pow, h2] using h3

end Bl.general_b_fact_upper_version
end
end

-- Source module: Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdRoot

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open NumberField IsDedekindDomain

theorem iroot_mem {R : Type} [CommRing R] [IsDomain R] (ζ : R) (M : ℕ) (P : Ideal R) (h1 : ζ ≠ 1) (hM : ζ ^ M = 1)
    (hP : ζ - 1 ∈ P) : (M : R) ∈ P := by
  first | exact Bl.general_b_fact_upper_version.goal1 .. | (apply Bl.general_b_fact_upper_version.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_upper_version.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper_version.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_upper_version.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper_version.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› ζ M P h1 hM hP | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› ζ M P h1 hM | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› ζ M P h1 | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› ζ M P | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› ζ M | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› ζ | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› | exact @Bl.general_b_fact_upper_version.goal1 R

theorem id_root : RootsOfUnityFormal := by
  intro R _ _ ζ N g1 g2 P1 P2 hN hζN hg1 hg2 hne hP1 hP2 h1 h2 hz1 hz2
  by_contra hζ
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨N, hN, hζN⟩
  have hMpos : 0 < orderOf ζ := orderOf_pos_iff.2 hfin
  have hM1 : ((orderOf ζ : ℕ) : R) ∈ P1 := iroot_mem ζ _ P1 hζ (pow_orderOf_eq_one ζ) hz1
  have hdvd : g1 ∣ orderOf ζ := by
    by_contra hnd
    exact id_coprime_notMem P1 hP1 g1 _ ((Nat.Prime.coprime_iff_not_dvd hg1).2 hnd) h1 hM1
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    omega
  have hklt : k < orderOf ζ := by
    rw [hk]
    have := hg1.two_le
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    nlinarith
  have hη : ζ ^ k ≠ 1 := pow_ne_one_of_lt_orderOf hk0 hklt
  have hηg : (ζ ^ k) ^ g1 = 1 := by
    rw [← pow_mul, mul_comm, ← hk]
    exact pow_orderOf_eq_one ζ
  have hηP : ζ ^ k - 1 ∈ P2 := by
    obtain ⟨w, hw⟩ := sub_dvd_pow_sub_pow ζ 1 k
    rw [one_pow] at hw
    rw [hw]
    exact P2.mul_mem_right _ hz2
  have hg1P2 : (g1 : R) ∈ P2 := iroot_mem (ζ ^ k) g1 P2 hη hηg hηP
  exact id_coprime_notMem P2 hP2 g2 g1 ((Nat.coprime_primes hg2 hg1).2 hne.symm) h2 hg1P2

theorem id_over : ExistsPrimeAbove := by
  intro E _ _ p hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    (Ideal.span_singleton_prime (Int.natCast_ne_zero.2 hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp) |>.isMaximal
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact Int.natCast_ne_zero.2 hp.ne_zero)
  obtain ⟨Q, hQ, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) (Ideal.span {(p : ℤ)}) (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective ℤ (𝓞 E))]
    exact bot_le)
  have hpQ : (p : 𝓞 E) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
      change (p : ℤ) ∈ Ideal.under ℤ Q
      rw [hc]; exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, ?_⟩, hpQ⟩
  rintro rfl
  exact (Nat.cast_ne_zero.2 hp.ne_zero) ((Submodule.mem_bot _).1 hpQ)

end Formalism.MainNotions.BridgeLemma

end
end
end

-- Source module: Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdUnit

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals NumberField Module IsDedekindDomain

theorem id_unit : ScalarRootOfUnity := by
  intro E _ _ _ S r T Λ F F' c hsc hzΛ hprim hcc hz hX
  have hz'o : F'.fl.z ∈ orth S (Xsp F) := by
    rw [p_mem_orth]
    intro x hx
    have hx' : x ∈ F'.fl.X := by rw [hX]; exact hx
    exact tie_X_le_ker F'.fl _ F'.fl.z_orth x hx'
  have hzo : F.fl.z ∈ orth S (Xsp F) := by
    rw [p_mem_orth]
    exact tie_X_le_ker F.fl _ F.fl.z_orth
  have hmem : c • F.fl.z ∈ Lsub Λ F := by
    unfold Lsub
    refine ⟨?_, (orth S (Xsp F)).smul_mem c hzo⟩
    have e : c • F.fl.z = F'.fl.z - (F'.fl.z - c • F.fl.z) := by abel
    rw [e]
    refine Submodule.sub_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right hz)
    exact ⟨hzΛ, hz'o⟩
  obtain ⟨o, ho⟩ := hprim c hmem
  refine ⟨o, ho, ?_⟩
  have hn : ∀ φ : E →+* ℂ, ‖φ (o : E)‖ = 1 := by
    intro φ
    have h1 := b_tau_norm hsc φ c
    rw [mul_comm, hcc, map_one] at h1
    have h2 : ‖φ c‖ ^ 2 = 1 := by exact_mod_cast h1.symm
    rw [ho]
    have h3 : 0 ≤ ‖φ c‖ := norm_nonneg _
    nlinarith
  obtain ⟨n, hn0, h⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ (x := (o : E)) o.isIntegral_coe hn
  refine ⟨n, hn0, ?_⟩
  apply RingOfIntegers.coe_injective
  simpa using h

theorem id_cong : ScalarCongruentOne := by
  intro E _ _ _ S r T Λ g F F' o hU hzΛ hadm hz P hg hT
  obtain ⟨ξ, _, hξ2, hξ3⟩ := hadm
  obtain ⟨s, hs, hw⟩ := hξ3 (Fin.last r) P hg

  have hzX : ∀ x ∈ Xsp F, S.hT F.fl.z x = 0 := fun x hx =>
    p_symm_zero S (tie_X_le_ker F.fl _ F.fl.z_orth x hx)
  have hze : ∀ a : Fin r, S.hT F.fl.z (F.fl.e a) = 0 := fun a => hzX _ (Submodule.subset_span ⟨a, rfl⟩)
  have h1 : S.hT F.fl.z F'.fl.z = (o : E) * (-(T : E)) := by
    have e : F'.fl.z = (F'.fl.z - (o : E) • F.fl.z) + (o : E) • F.fl.z := by abel
    rw [e, map_add (f := _), hzX _ hz, zero_add, map_smul, smul_eq_mul, F.fl.z_norm]
  have h2 : S.hT F.fl.z (frameAct (frame F) ξ (Fin.last r)) = -(T : E) := by
    unfold frameAct

    rw [map_sum, Fin.sum_univ_castSucc]
    have hl : frame F (Fin.last r) = F.fl.z := by simp [FlagG.fvec]
    have hc : ∀ a : Fin r, frame F a.castSucc = F.fl.e a := fun a => by simp [FlagG.fvec]
    rw [hl, hξ2, map_smul, F.fl.z_norm]
    have : ∑ a : Fin r, S.hT F.fl.z (((ξ a.castSucc (Fin.last r) : 𝓞 E) : E) • frame F a.castSucc) = 0 :=
      Finset.sum_eq_zero fun a _ => by rw [hc, map_smul, hze, smul_zero]
    rw [this, zero_add]
    simp
  have h3 : S.hT F.fl.z (frame F' (Fin.last r) - frameAct (frame F) ξ (Fin.last r)) =
      -(((o - 1 : 𝓞 E) : E) * (T : E)) := by
    have hl : frame F' (Fin.last r) = F'.fl.z := by simp [FlagG.fvec]
    rw [map_sub, hl, h1, h2]
    push_cast
    ring

  have h4 : ∀ y ∈ Ideal.span {(g : 𝓞 E)} • Λ, ∃ a : 𝓞 E, S.hT F.fl.z y = (((g : 𝓞 E) * a : 𝓞 E) : E) := by
    intro y hy
    rw [Submodule.ideal_span_singleton_smul] at hy
    obtain ⟨l, hl, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
    have hd : l ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by rw [hU]; exact hl
    obtain ⟨a, ha⟩ := d_mem_dual.1 hd _ hzΛ
    refine ⟨a, ?_⟩
    rw [← algebraMap_smul E (g : 𝓞 E) l, map_smul, smul_eq_mul, ← ha]
    push_cast
    rfl
  obtain ⟨a, ha⟩ := h4 _ hw
  rw [← algebraMap_smul E s, map_smul, smul_eq_mul, h3] at ha
  have h5 : s * ((o - 1) * (T : 𝓞 E)) = -((g : 𝓞 E) * a) := by
    apply RingOfIntegers.coe_injective
    have : (algebraMap (𝓞 E) E s) * (((o - 1 : 𝓞 E) : E) * (T : E)) = -(((g : 𝓞 E) * a : 𝓞 E) : E) := by
      rw [← ha]; ring
    simpa using this
  have h6 : s * ((o - 1) * (T : 𝓞 E)) ∈ P.asIdeal := by
    rw [h5]
    exact P.asIdeal.neg_mem (P.asIdeal.mul_mem_right _ hg)
  rcases P.isPrime.mem_or_mem h6 with h | h
  · exact absurd h hs
  · rcases P.isPrime.mem_or_mem h with h | h
    · exact h
    · exact absurd h hT

end Formalism.MainNotions.BridgeLemma

end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsIdentityOfEqualFlags

section

@[expose] public section

noncomputable section

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints Formalism.MainNotions.LatticeGluingRadicals
  Formalism.MainNotions.BridgeLemma

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ZsC1c

variable {D : D7} {X : HidaSetting D}

theorem isIdentity_of_equal_flags (hTg : ∀ u : D.what₂.Word, (D.mem u).A.T ≠ D.host.g 0 ∧ (D.mem u).A.T ≠ D.host.g 1)
    (Y : Full X) {u : D.what₂.Word} (t : GTu Y u)
    (hXa : ∀ a, (frq X t.rep).fl.Xa a = (lf D (X.Fu u)).fl.Xa a)
    (hXp : (frq X t.rep).fl.Xplus = (lf D (X.Fu u)).fl.Xplus)
    (hrel : Relevant D.host.F (lf D (X.Fu u)).fl (frq X t.rep).fl) : t.isId := by
  have hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (tie_Tu_pos D u).ne'
  have hrow : IsRowLat D (X.Fu u) t.lam := (Y.rowsOK u).1 t.lam t.mem
  have hfix : FixedHyp D t.lam (lf D (X.Fu u)) := hrow.2.1
  have hPD : TermDef.PD D t.lam (lf D (X.Fu u)) u (frq X t.rep) := t.rep.2.2.2.2
  have hlift : IsLift t.lam (frq X t.rep) := hPD.1
  have hadm : IsAdmissible t.lam (gS D) (lf D (X.Fu u)) (frq X t.rep) := hPD.2.1
  have hconv : IsFixedConv t.lam (gS D) (frq X t.rep) := hPD.2.2.1
  obtain ⟨c, hcc, he, hz⟩ := id_scal D.host.F D.host.E (hS D) D.R.rS _ (lf D (X.Fu u)).fl (frq X t.rep).fl hT0
    (tie_trace D.sp.cm) hXa hXp hrel
  have hX : (frq X t.rep).fl.X = (lf D (X.Fu u)).fl.X := by rw [tie_X_eq_Xa, tie_X_eq_Xa]; exact hXa _
  obtain ⟨o, ho, N, hN, hoN⟩ := id_unit D.host.E (hS D) D.R.rS _ t.lam (lf D (X.Fu u)) (frq X t.rep) c (p_starConj D)
    hlift.1 hfix.2.2.2.2 hcc hz hX
  have hcong : ∀ i : Fin 2, ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      o - 1 ∈ P.asIdeal := by
    intro i P hP
    refine id_cong D.host.E (hS D) D.R.rS (Tu D u) t.lam (gS D) (lf D (X.Fu u)) (frq X t.rep) o hfix.2.1
      hfix.2.2.1.1 hadm (by rw [ho]; exact hz) P ?_ ?_
    · unfold gS
      rw [Nat.cast_mul]
      fin_cases i
      · exact P.asIdeal.mul_mem_right _ hP
      · exact P.asIdeal.mul_mem_left _ hP
    · refine id_coprime_notMem P.asIdeal P.isPrime.ne_top _ _ ?_ hP
      refine (Nat.coprime_primes (D.host.g_prime i) (D.mem u).A.T_prime).2 ?_
      fin_cases i
      · exact (hTg u).1.symm
      · exact (hTg u).2.symm
  obtain ⟨P1, hP1⟩ := id_over D.host.E _ (D.host.g_prime 0)
  obtain ⟨P2, hP2⟩ := id_over D.host.E _ (D.host.g_prime 1)
  have ho1 : o = 1 := id_root (𝓞 D.host.E) o N _ _ P1.asIdeal P2.asIdeal hN hoN (D.host.g_prime 0) (D.host.g_prime 1)
    D.host.g_ne P1.isPrime.ne_top P2.isPrime.ne_top hP1 hP2 (hcong 0 P1 hP1) (hcong 1 P2 hP2)
  have hc1 : c = 1 := by rw [← ho, ho1]; rfl
  subst hc1
  simp only [one_smul] at he hz
  obtain ⟨n, hn, hne⟩ := id_lift D _ t.lam (lf D (X.Fu u)) (frq X t.rep) hfix hlift hconv he hz
  have hzo : (lf D (X.Fu u)).fl.z ∈ orth (hS D) (Xsp (lf D (X.Fu u))) := by
    rw [p_mem_orth]
    exact tie_X_le_ker _ _ (lf D (X.Fu u)).fl.z_orth
  have h3' := hn.2.2 _ hzo
  have hzz : n (lf D (X.Fu u)).fl.z - (frq X t.rep).fl.z =
      (n (lf D (X.Fu u)).fl.z - (lf D (X.Fu u)).fl.z) - ((frq X t.rep).fl.z - (lf D (X.Fu u)).fl.z) := by abel
  refine ⟨frq X t.rep, TermDef.rep_mk (⟨frq X t.rep, hPD⟩ : TermDef.Carrier (TermDef.PD D t.lam (lf D (X.Fu u)) u)),
    n, hn, hne, ?_⟩
  rw [hzz]
  exact Submodule.sub_mem _ h3' hz

theorem one_le_index_of_relevant (hTg : ∀ u : D.what₂.Word, (D.mem u).A.T ≠ D.host.g 0 ∧ (D.mem u).A.T ≠ D.host.g 1)
    (Y : Full X) {u : D.what₂.Word} (t : GTu Y u) (ht : t ∈ relSet Y u) : 1 ≤ jT t := by
  obtain ⟨hr, hG, hid⟩ := relevantSet_zeroG_not_identity ht
  obtain ⟨j, hj, c, hN⟩ := exists_nfFull_of_relevant_of_G_eq_zero Y t hr hG
  rw [index_eq_normalForm t hN]
  by_contra hj0
  have hj0 : j = 0 := by omega
  subst hj0
  obtain ⟨k1, -, k3⟩ := Formalism.HermitianLatticeCounting.Final.S6.nFJZero _ _ _ _ _ _ c hN.1
  have hXa : ∀ a, (frq X t.rep).fl.Xa a = (lf D (X.Fu u)).fl.Xa a := fun a => by
    exact (nf_Xa (frq X t.rep).fl (nf_T_ne D u) a).symm.trans
      ((k1 a).trans (nf_Xa (lf D (X.Fu u)).fl (fixedFlag_level_ne_zero D u) a))
  have k3' : (frq X t.rep).fl.z - c • (lf D (X.Fu u)).fl.z ∈ (lf D (X.Fu u)).fl.X := by
    rw [← normal_form_z_eq (frq X t.rep).fl (nf_T_ne D u),
      ← normal_form_z_eq (lf D (X.Fu u)).fl (fixedFlag_level_ne_zero D u),
      ← nf_X (lf D (X.Fu u)).fl (fixedFlag_level_ne_zero D u)]
    exact k3
  have hXp : (frq X t.rep).fl.Xplus = (lf D (X.Fu u)).fl.Xplus :=
    nf_Xplus_eq _ _ (by rw [nf_X_eq, nf_X_eq]; exact hXa _) c hN.1.1 k3'
  exact hid (isIdentity_of_equal_flags hTg Y t hXa hXp (relRepC D X Y u u t hr hG).1)

end ZsC1c

theorem JPosC_holds : JPosC := by
  intro Cg cb Cw cT CT C0 C' Cl D large₂ X Y u hK _ t ht
  refine one_le_index_of_relevant (fun w => ?_) Y t ht

  have hc : Nat.Coprime (D.mem w).A.T (D.host.g 0 * D.host.g 1) := (hK.2.2.2.2.2.2.1 w).2
  have key : ∀ i : Fin 2, D.host.g i ∣ D.host.g 0 * D.host.g 1 → (D.mem w).A.T ≠ D.host.g i := by
    intro i hd h
    rw [h] at hc
    have h1 : Nat.Coprime (D.host.g i) (D.host.g i) := Nat.Coprime.coprime_dvd_right hd hc
    exact (D.host.g_prime i).one_lt.ne' (by simpa [Nat.coprime_self] using h1)
  exact ⟨key 0 (dvd_mul_right _ _), key 1 (dvd_mul_left _ _)⟩

end Formalism.L2.SG.KappaOffDiagonal
end
end
end
