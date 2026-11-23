module

public import Formalism.PeriodIntegrals.NormRepChange
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXFinsetSum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXOfMemXS
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.NlamFrameMem
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
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.NlamFrameMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.IsLoUniConjTranspose
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.StepGram
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.GlobEntry

section

@[expose] public section

noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.PairValDefs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem glob_entry (D : D7) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ NLam Λ G) (hXS : XLam Λ G = XS D G.fl) (hz : G.fl.z ∈ Λ)
    (a : Fin (D.R.rS + 1)) (h : a.val + 1 < D.R.rS + 1) :
    ∀ δ ∈ ddS D, ∃ o : 𝓞 D.host.E, (o : D.host.E) = fmat D G n a ⟨a.val + 1, h⟩ * δ := by
  have ha : a.val < D.R.rS := by omega
  have hf : fmat D G n a ⟨a.val + 1, h⟩ =
      G.fl.coefX (n (frame G ⟨a.val + 1, h⟩) - frame G ⟨a.val + 1, h⟩) ⟨a.val, ha⟩ := by
    simp only [fmat, dif_pos ha]
    rw [if_neg (by intro e; have := congrArg Fin.val e; simp at this), zero_add]
  rw [hf]
  have hXSΛ : ∀ v, v ∈ XS D G.fl → v ∈ Λ := by
    intro v hv
    rw [← hXS, XLam, Submodule.mem_inf] at hv
    exact hv.1
  by_cases hr : a.val + 1 < D.R.rS
  · have hfi : frame G ⟨a.val + 1, h⟩ = G.fl.e ⟨a.val + 1, hr⟩ := by
      rw [show (⟨a.val + 1, h⟩ : Fin (D.R.rS + 1)) = (⟨a.val + 1, hr⟩ : Fin D.R.rS).castSucc from Fin.ext rfl,
        frame_castSucc]
    rw [hfi]
    apply frac_lemma D _ (-((D.R.rS : ℤ) - ((a.val + 1 : ℕ) : ℤ)))
    intro x hx
    have hxe : x • G.fl.e ⟨a.val + 1, hr⟩ ∈ XS D G.fl := Submodule.subset_span ⟨⟨a.val + 1, hr⟩, x, hx, rfl⟩
    have hn1 : n (x • G.fl.e ⟨a.val + 1, hr⟩) ∈ XS D G.fl := by
      rw [← hXS, XLam, Submodule.mem_inf]
      exact ⟨nlam_mem hn (hXSΛ _ hxe), nlam_X hn (Submodule.smul_mem _ x (e_mem_X _ _))⟩
    have hc := (coefX_of_mem_XS D G.fl hn1).2 ⟨a.val, ha⟩
    have hd : n (G.fl.e ⟨a.val + 1, hr⟩) - G.fl.e ⟨a.val + 1, hr⟩ ∈ G.fl.X :=
      Xa_le_X _ _ ((nlam_frame_mem G hn).1 _)
    have hsplit : n (x • G.fl.e ⟨a.val + 1, hr⟩) =
        x • (G.fl.e ⟨a.val + 1, hr⟩ + (n (G.fl.e ⟨a.val + 1, hr⟩) - G.fl.e ⟨a.val + 1, hr⟩)) := by
      rw [map_smul]; congr 1; abel
    rw [hsplit, coefX_smul _ (add_mem (e_mem_X _ _) hd), coefX_add _ (e_mem_X _ _) hd, coefX_e,
      if_neg (by intro e; have := congrArg Fin.val e; simp at this), zero_add] at hc
    have hexp : -((D.R.rS : ℤ) - ((a.val + 1 : ℕ) : ℤ)) - 1 =
        -((D.R.rS : ℤ) - (((⟨a.val, ha⟩ : Fin D.R.rS) : ℕ) : ℤ)) := by
      push_cast; ring
    rw [hexp]
    exact hc
  · have hfz : frame G ⟨a.val + 1, h⟩ = G.fl.z := by
      rw [show (⟨a.val + 1, h⟩ : Fin (D.R.rS + 1)) = Fin.last _ from Fin.ext (by simp; omega), frame_last]
    rw [hfz]
    apply frac_lemma D _ 0
    intro x hx
    rw [zpow_zero] at hx
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hx
    have hv : n G.fl.z - G.fl.z ∈ XS D G.fl := by
      rw [← hXS, XLam, Submodule.mem_inf]
      exact ⟨sub_mem (nlam_mem hn hz) hz, (nlam_frame_mem G hn).2⟩
    have hc := (coefX_of_mem_XS D G.fl hv).2 ⟨a.val, ha⟩
    have hexp : (0 : ℤ) - 1 = -((D.R.rS : ℤ) - (((⟨a.val, ha⟩ : Fin D.R.rS) : ℕ) : ℤ)) := by
      push_cast; omega
    rw [hexp, ← Algebra.smul_def]
    exact fi_smul _ o hc

theorem stepGlob (D : D7) : StepGlob D := by
  intro Λ T G n hn hXS hz δ hδ
  have hmem : sgUp (fmat D G n) * δ ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    unfold sgUp
    rw [Finset.sum_mul]
    apply Subring.sum_mem
    intro a _
    split_ifs with h
    · obtain ⟨o, ho⟩ := glob_entry D Λ G n hn hXS hz a h δ hδ
      exact ⟨o, ho⟩
    · rw [zero_mul]; exact Subring.zero_mem _
  obtain ⟨o, ho⟩ := hmem
  exact ⟨o, ho⟩

end PI.NRCW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.NormRepMoveOfSteps

section

@[expose] public section

noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.PairValDefs Matrix IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem normRepMove_of_steps (D : D7) (u u' : D.what₂.Word) (hE : TermEqIff D u u')
    (h1 : StepExp D) (h2 : StepGram D) (h3 : StepGlob D) (h4 : StepLoc D) (h5 : StepTr D) :
    PI.NormRepChange.NormRepMove D u u' := by
  intro F0 Λ hΛ t _hrel F₁ F₂ hR1 hA1 hR2 hA2 w _hw
  obtain ⟨p1, e1⟩ := hR1
  obtain ⟨p2, e2⟩ := hR2
  have hDC : DCRel Λ (lf D F0) F₁ F₂ :=
    ((hE F0 Λ hΛ) ⟨F₁, p1⟩ ⟨F₂, p2⟩).mp (e1.trans e2.symm)
  obtain ⟨n, hn, m, hm, hfr, -⟩ := hDC
  obtain ⟨hNu, hNe⟩ := h1 Λ (lf D F0) n hn
  obtain ⟨hMu, hMe⟩ := h1 Λ F₁ m hm
  have hG := h2 (lf D F0) F₁ F₂ n m (fmat D (lf D F0) n) (fmat D F₁ m) hn.1.1 hNe hMe hfr
  obtain ⟨A, B, hA, hB, hZ, hs⟩ := core_Z _ _ _ _ hNu hMu hG
  refine ⟨A, B, hA, hB, hZ, ?_⟩
  rw [hs]
  obtain ⟨_, ⟨_, _, hLift0, hConv0⟩, hXS0⟩ := hΛ
  obtain ⟨hLift1, _, hConv1, hXS1⟩ := p1
  have hglob : ∀ δ ∈ ddS D, ∃ o : 𝓞 D.host.E,
      (o : D.host.E) = (sgUp (fmat D (lf D F0) n) + sgUp (fmat D F₁ m)) * δ := by
    intro δ hδ
    obtain ⟨o1, ho1⟩ := h3 Λ (lf D F0) n hn hXS0 hLift0.1 δ hδ
    obtain ⟨o2, ho2⟩ := h3 Λ F₁ m hm hXS1 hLift1.1 δ hδ
    exact ⟨o1 + o2, by rw [add_mul, ← ho1, ← ho2]; norm_cast⟩
  have hloc := h4 Λ (lf D F0) F₁ F₂ n m hn hm hfr hConv0 hConv1 hA1 hA2 hLift0.1 hLift1.1
  obtain ⟨k, hk⟩ := h5 _ hglob hloc
  exact psiInf_of_trace (gS D) _ _ k hk

end PI.NRCW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.TraceIntOfMulDd

section

@[expose] public section

noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.PairValDefs IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gS_ne_zero (D : D7) : gS D ≠ 0 := by
  show D.host.g 0 * D.host.g 1 ≠ 0
  exact mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

theorem coe_algebraMap_OF (D : D7) (δ : 𝓞 D.host.F) :
    ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) δ : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F D.host.E (δ : D.host.F) := rfl

theorem trace_int_of_mul_dd (D : D7) (x : D.host.E)
    (hx : ∀ δ ∈ ddS D, ∃ o : 𝓞 D.host.E, (o : D.host.E) = x * δ) :
    ∃ k : ℤ, Algebra.trace ℚ D.host.E x = k := by
  have ha : ∀ δ ∈ differentIdeal ℤ (𝓞 D.host.F),
      ∃ a : 𝓞 D.host.F, (a : D.host.F) = (δ : D.host.F) * Algebra.trace D.host.F D.host.E x := by
    intro δ hδ
    have hmem : algebraMap D.host.F D.host.E (δ : D.host.F) ∈ ddS D := by
      unfold ddS
      rw [FractionalIdeal.mem_coeIdeal]
      exact ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) δ, Ideal.mem_map_of_mem _ hδ, coe_algebraMap_OF D δ⟩
    obtain ⟨o, ho⟩ := hx _ hmem
    have htr : Algebra.trace D.host.F D.host.E (o : D.host.E) = (δ : D.host.F) * Algebra.trace D.host.F D.host.E x := by
      rw [ho, mul_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
    have hint : IsIntegral ℤ (Algebra.trace D.host.F D.host.E (o : D.host.E)) :=
      Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe o)
    rw [htr] at hint
    exact ⟨⟨_, hint⟩, rfl⟩
  have hdual : Algebra.trace D.host.F D.host.E x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) := by
    rw [← inv_inv (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F)), ← coeIdeal_differentIdeal ℤ ℚ D.host.F,
      FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot)]
    intro y hy
    obtain ⟨y', hy', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
    obtain ⟨a, ha'⟩ := ha y' hy'
    rw [FractionalIdeal.mem_one_iff]
    exact ⟨a, by rw [mul_comm]; exact ha'⟩
  rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) ≠ 0)] at hdual
  obtain ⟨k, hk⟩ := hdual 1 (FractionalIdeal.one_mem_one _)
  refine ⟨k, ?_⟩
  have h1 : Algebra.traceForm ℚ D.host.F (Algebra.trace D.host.F D.host.E x) 1 = Algebra.trace ℚ D.host.F (Algebra.trace D.host.F D.host.E x) := by
    rw [Algebra.traceForm_apply, mul_one]
  rw [← Algebra.trace_trace (S := D.host.F), ← h1, ← hk]
  simp

theorem stepTr (D : D7) : StepTr D := by
  intro y hy hP
  have hg0 : (gS D : D.host.E) ≠ 0 := by exact_mod_cast gS_ne_zero D
  have hint : ∀ δ ∈ ddS D, ∃ o : 𝓞 D.host.E, (o : D.host.E) = y / (gS D : D.host.E) * δ := by
    intro δ hδ
    obtain ⟨o, ho⟩ := hy δ hδ
    have hδint : ∃ d' : 𝓞 D.host.E, (d' : D.host.E) = δ := by
      unfold ddS at hδ
      obtain ⟨d', -, hd'⟩ := (FractionalIdeal.mem_coeIdeal _).mp hδ
      exact ⟨d', hd'⟩
    obtain ⟨d', rfl⟩ := hδint
    have hval : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
        P.valuation D.host.E (y / (gS D : D.host.E) * d') ≤ 1 := by
      intro P
      by_cases hPg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
      · rw [map_mul]
        exact mul_le_one' (hP P hPg) (P.valuation_le_one d')
      · have h1 : P.valuation D.host.E ((gS D : ℕ) : D.host.E) = 1 := by
          have h2 := (P.valuation_eq_one_iff_notMem (K := D.host.E)).mpr hPg
          simpa using h2
        have e : y / (gS D : D.host.E) * d' = (y * d') / (gS D : D.host.E) := by ring
        rw [e, map_div₀, h1, div_one, ← ho]
        exact P.valuation_le_one o
    obtain ⟨o', ho'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (h := hval)
    exact ⟨o', ho'⟩
  obtain ⟨k, hk⟩ := trace_int_of_mul_dd D (y / (gS D : D.host.E)) hint
  refine ⟨k, ?_⟩
  have e : y = ((gS D : ℚ)) • (y / (gS D : D.host.E)) := by
    rw [Algebra.smul_def, map_natCast]
    field_simp
  rw [e, LinearMap.map_smul, hk, smul_eq_mul]

end PI.NRCW
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NormRepChange

section

@[expose] public section

noncomputable section

open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem norm_representative_move (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) (hS : Formalism.L2.SG.TermDef.TermStable D u u') (hE : Formalism.L2.SG.TermDef.TermEqIff D u u') (hF : Formalism.L2.SG.TermDef.TermFun D u u') (hP : Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u')) (hsig : (Formalism.MainNotions.S.VS D).SigOK) : PI.NormRepChange.NormRepMove D u u' :=
  PI.NRCW.normRepMove_of_steps D u u' hE (PI.NRCW.stepExp D) (PI.NRCW.stepGram D) (PI.NRCW.stepGlob D)
    (PI.NRCW.stepLoc D) (PI.NRCW.stepTr D)
end
end
end
