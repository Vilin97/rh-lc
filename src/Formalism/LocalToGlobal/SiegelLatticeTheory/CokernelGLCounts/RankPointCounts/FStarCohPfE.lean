module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfD
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsDenominatorSecond

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching IsDedekindDomain ValuativeRel

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

namespace CohIntPf

variable {D : Formalism.BasicNotions.D7}

theorem exists_den {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ) (x : (VS D).V) :
    ∃ d : 𝓞 D.host.F, d ≠ 0 ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) d • x ∈ Λ :=
  _root_.UpperTheory.Reformulated.B.ExistsBaseFieldIntegerDenominator.exists_den hΛ x

variable (Zd : LocDat D)

theorem bcP_mem_cof {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ) (x : (VS D).V) :
    {p : PlF D | baseChange₂ D p x ∉ lattice₂ D Zd.M p Λ}.Finite := by
  obtain ⟨d, hd, hdx⟩ := exists_den hΛ x
  have hI : Ideal.span {d} ≠ (0 : Ideal (𝓞 D.host.F)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hd
  refine (Ideal.finite_factors hI).subset fun p hp => ?_
  simp only [Set.mem_ofPred_eq] at hp ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  by_contra hnd
  apply hp
  have := p.isPrime
  rw [Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd p hΛ.toIsLattice]
  exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal Λ x).2 ⟨d, hnd, hdx⟩

theorem scal_mem {p : PlF D} (hs : (Zd.M p).split = none)
    (hδ : Zd.δ p ∈ 𝒪[(D.s.atP p).Fp] ∧ (Zd.δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp])
    (hu : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O ∧ (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O)
    (b : Fin (D.R.rS + 1)) : TermLoc.sgnP' D p b * frFac Zd.δ p b ∈ (D.s.atP p).O := by
  have hs' : (D.s.atP p).split = none := by
    have hA := (Zd.agree p).2.2.2.2.2
    rw [hs] at hA
    cases h2 : (D.s.atP p).split with
    | none => rfl
    | some sg =>
      rw [h2] at hA
      exact (hA : False).elim
  refine Subring.mul_mem _ ?_ ?_
  · unfold TermLoc.sgnP'
    rw [hs']
    exact Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _
  · rw [Formalism.L2.SG.Pf.BBTie.bt_frFac_eq Zd p b]
    set w : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p)⁻¹ *
      (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) with hw
    have hwO : w ∈ (D.s.atP p).O :=
      Subring.mul_mem _ (Formalism.L2.SG.Pf.LocalDenominators.alg_mem_O (D.s.atP p) hδ.2) hu.2
    have hinv : (((Formalism.L2.SG.Pf.BBTie.bt_T_unit Zd p).unit⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) = w := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [IsUnit.unit_spec]
      show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p) * (D.s.atP p).ιE (uP p : D.host.E) * w = 1
      rw [hw]
      have hδ0 : Zd.δ p ≠ 0 := (Zd.agree p).2.1
      have hu0 := Formalism.L2.SG.Pf.BBTie.uP_ne (D := D) p
      calc algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p) * (D.s.atP p).ιE (uP p : D.host.E) *
            (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p)⁻¹ * (D.s.atP p).ιE ((uP p : D.host.E)⁻¹))
          = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p * (Zd.δ p)⁻¹) *
            (D.s.atP p).ιE ((uP p : D.host.E) * (uP p : D.host.E)⁻¹) := by rw [map_mul, map_mul]; ring
        _ = 1 := by rw [mul_inv_cancel₀ hδ0, mul_inv_cancel₀ hu0, map_one, map_one, mul_one]
    rw [Units.val_pow_eq_pow_val, hinv]
    exact Subring.pow_mem _ hwO _

end CohIntPf

open CohIntPf

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem cohInt_holds : CohInt Zd u u' F0 what₂ := by
  intro hP γ Z F'₂ φ' _
  have hgen := (hP.2.1.1 γ.lam γ.mem).1
  have hΛ : Submodule.IsFullLattice D.host.E γ.lam := by
    letI : Submodule.IsLattice D.host.E γ.lam := hgen.1
    have h0 : Submodule.span D.host.E ((VS D).L0 : Set (VS D).V) = ⊤ := by
      apply top_unique
      intro x _
      have hx : (Formalism.L2.SG.InstExistsPf.crdE D).symm x ∈
          Submodule.span D.host.E (Formalism.L2.SG.InstExistsPf.Lv D : Set _) := by
        rw [Formalism.L2.SG.InstExistsPf.L_span]; trivial
      have hh : ∀ y ∈ Submodule.span D.host.E (Formalism.L2.SG.InstExistsPf.Lv D : Set _),
          Formalism.L2.SG.InstExistsPf.crdE D y ∈ Submodule.span D.host.E ((VS D).L0 : Set _) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy => exact Submodule.subset_span hy
        | zero => simp
        | add x y _ _ hx hy => exact add_mem hx hy
        | smul a x _ hx => simpa using Submodule.smul_mem _ a hx
      simpa using hh _ hx
    obtain ⟨p, hp⟩ := Ideal.exists_maximal (α := 𝓞 D.host.E)
    letI : p.IsPrime := hp.isPrime
    obtain ⟨g, hg, he⟩ := hgen.2 p hp
    have hmap : ∀ x ∈ (VS D).L0, g x ∈ Submodule.span D.host.E (γ.lam : Set _) := by
      intro x hx
      have hx' : g x ∈ Formalism.HermitianLatticesTheory.loc (K := D.host.E) p γ.lam := by
        rw [← he, Formalism.HermitianLatticesTheory.isomAct_mem_gmap, LinearEquiv.symm_apply_apply]
        exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ hx
      obtain ⟨s, hs, hsx⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp hx'
      have hs0 : algebraMap (𝓞 D.host.E) D.host.E s ≠ 0 := by
        intro hz
        have : s = 0 := (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (by simpa using hz)
        subst s
        exact (Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem p 0 hs) (Ideal.zero_mem p)
      have hmem := Submodule.subset_span hsx
      have := Submodule.smul_mem (Submodule.span D.host.E (γ.lam : Set _))
        (algebraMap (𝓞 D.host.E) D.host.E s)⁻¹ hmem
      simpa [Algebra.smul_def, ← smul_assoc, hs0] using this
    refine ⟨?_⟩
    apply top_unique
    intro x _
    have hx : g.symm x ∈ Submodule.span D.host.E ((VS D).L0 : Set _) := by rw [h0]; trivial
    have hh : ∀ y ∈ Submodule.span D.host.E ((VS D).L0 : Set _),
        g y ∈ Submodule.span D.host.E (γ.lam : Set _) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact hmap y hy
      | zero => simp
      | add x y _ _ hx hy => simpa using add_mem hx hy
      | smul a x _ hx => simpa using Submodule.smul_mem _ a hx
    simpa using hh _ hx
  have hgood := Formalism.L2.SG.Pf.LocModel.good_cofinite Zd.δ Zd.M Zd.agree ∅
  rw [Filter.eventually_cofinite] at hgood
  refine (hgood.union (Set.finite_iUnion fun b => bcP_mem_cof Zd hΛ (frame F'₂ b))).subset ?_
  intro p hp
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, not_or, not_exists, not_not] at hn
  obtain ⟨hg, hb⟩ := hn
  apply hp
  intro b
  exact Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Zd p (scal_mem Zd hg.1 hg.2.1 hg.2.2.1 b) (hb b)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
