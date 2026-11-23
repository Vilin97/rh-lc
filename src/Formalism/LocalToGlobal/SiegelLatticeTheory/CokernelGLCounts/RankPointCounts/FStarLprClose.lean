module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaK
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLocInB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFrameIota
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaF
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprPfC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfM
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfD
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfF
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfG
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Corank
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScalEquivGen
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScalRelRepFree
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprPfD
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarMinors
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.GenericityConstantDoubleCosets

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprExistA

section

@[expose] public section

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel
  Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.LprEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Glob

variable {D : D7}

theorem LprExistA_iso_span {s : Set (VS D).V} (h : ∀ x ∈ s, ∀ y ∈ s, (VS D).hT x y = 0) :
    ∀ x ∈ Submodule.span D.host.E s, ∀ y ∈ Submodule.span D.host.E s, (VS D).hT x y = 0 := by
  have h1 : ∀ x ∈ s, ∀ y ∈ Submodule.span D.host.E s, (VS D).hT x y = 0 := by
    intro x hx y hy
    have hle : Submodule.span D.host.E s ≤ LinearMap.ker ((VS D).hT x) := by
      rw [Submodule.span_le]
      intro y' hy'
      exact h x hx y' hy'
    exact hle hy
  intro x hx y hy
  have hle : Submodule.span D.host.E s ≤ LinearMap.ker ((VS D).hT.flip y) := by
    rw [Submodule.span_le]
    intro x' hx'
    show (VS D).hT.flip y x' = 0
    rw [LinearMap.flip_apply]
    exact h1 x' hx' y hy
  have := hle hx
  rw [LinearMap.mem_ker, LinearMap.flip_apply] at this
  exact this

theorem LprExistA_orth_span {s : Set (VS D).V} {x : (VS D).V} (h : ∀ v ∈ s, (VS D).hT v x = 0) :
    ∀ v ∈ Submodule.span D.host.E s, (VS D).hT v x = 0 := by
  intro v hv
  have hle : Submodule.span D.host.E s ≤ LinearMap.ker ((VS D).hT.flip x) := by
    rw [Submodule.span_le]
    intro v' hv'
    show (VS D).hT.flip x v' = 0
    rw [LinearMap.flip_apply]
    exact h v' hv'
  have := hle hv
  rw [LinearMap.mem_ker, LinearMap.flip_apply] at this
  exact this

theorem gfacts_move {Λ : Submodule (𝓞 D.host.E) (VS D).V} {f g1 g2 g2' : Fin (D.R.rS + 1) → (VS D).V}
    {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hG : GFacts Λ f g1 g2' β)
    (hX : Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) =
      Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc))
    (hsp : Submodule.span D.host.E (Set.range g2') = Submodule.span D.host.E (Set.range g2))
    (hz : g2' (Fin.last _) - g2 (Fin.last _) ∈
      Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc))
    (ht : GDl f g2' (D.R.rS + 1) = GDl f g2 (D.R.rS + 1)) (hr : GDl f g2' D.R.rS = GDl f g2 D.R.rS)
    (ho' : Gom' f g2' = Gom' f g2) (ho : Gom f g2' = Gom f g2) : GFacts Λ f g1 g2 β := by
  have hmap : Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) ≤
      (Submodule.span D.host.E (Set.range fun a : Fin D.R.rS => g1 a.castSucc)).comap
        β.symm.toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact hG.xmap' b
  refine
    { iso := hG.iso
      lam := hG.lam
      lam' := hG.lam'
      xmap := fun a => hX ▸ hG.xmap a
      xmap' := fun a => ?_
      zmap := ?_
      fiso := hG.fiso
      g2iso := fun a b => ?_
      proj := hG.proj
      gram := hG.gram
      theta := fun x1 hx1 => ?_
      ratio := ?_
      omp := ?_
      om := ?_ }
  · have h : g2 a.castSucc ∈ Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) := by
      rw [hX]; exact Submodule.subset_span ⟨a, rfl⟩
    exact hmap h
  · have h1 := hG.zmap
    rw [hX] at h1
    have h3 := Submodule.add_mem _ h1 hz
    rwa [sub_add_sub_cancel] at h3
  · have hiso : ∀ x ∈ Set.range (fun b : Fin D.R.rS => g2' b.castSucc),
        ∀ y ∈ Set.range (fun b : Fin D.R.rS => g2' b.castSucc), (VS D).hT x y = 0 := by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact hG.g2iso i j
    have ha : g2 a.castSucc ∈ Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) := by
      rw [hX]; exact Submodule.subset_span ⟨a, rfl⟩
    have hb : g2 b.castSucc ∈ Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) := by
      rw [hX]; exact Submodule.subset_span ⟨b, rfl⟩
    exact LprExistA_iso_span hiso _ ha _ hb
  · obtain ⟨x2, h1, h2, h3⟩ := hG.theta x1 hx1
    refine ⟨x2, fun i => ?_, h2, hX ▸ h3⟩
    rcases i with a | b
    · exact h1 (Sum.inl a)
    · have horth : ∀ v ∈ Set.range g2', (VS D).hT v x2 = 0 := by
        rintro _ ⟨c, rfl⟩
        exact h1 (Sum.inr c)
      have hb : g2 b ∈ Submodule.span D.host.E (Set.range g2') := by
        rw [hsp]; exact Submodule.subset_span ⟨b, rfl⟩
      exact LprExistA_orth_span horth _ hb
  · rw [← ht, ← hr]; exact hG.ratio
  · rw [← ht, ← ho']; exact hG.omp
  · rw [← ht, ← ho, ← hX]; exact hG.om

theorem gfacts_frameAct {Λ : Submodule (𝓞 D.host.E) (VS D).V} {f g1 h : Fin (D.R.rS + 1) → (VS D).V}
    {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) (hG : GFacts Λ f g1 (frameAct h ξ⁻¹) β) :
    GFacts Λ f g1 h β := by
  have hη := inv_unitri ξ h1 h2
  refine gfacts_move hG (Xs_frameAct_inv h ξ h1 h2) (span_frameAct_inv h ξ h1 h2) ?_
    (GDl_frameAct_top f h ξ⁻¹ hη.1 hη.2) (GDl_frameAct_r f h ξ⁻¹ hη.1 hη.2)
    (Gom'_frameAct f h ξ⁻¹ hη.1 hη.2) (Gom_frameAct f h ξ⁻¹ hη.1 hη.2)
  exact frameAct_last_sub h ξ⁻¹ (hη.2 _)

end Glob

section LocIota

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

theorem iotaG_congr {q : E} {abelian₂ : Submodule M.L.O V} {r : ℕ} {f₀ f₁ f₂ f₂' : Fin (r + 1) → V} {e : V ≃ₗ[E] V}
    (hX : H.X f₂ = H.X f₂') (h : IotaG H q abelian₂ f₀ f₁ f₂ e) : IotaG H q abelian₂ f₀ f₁ f₂' e := by
  unfold IotaG at h ⊢
  rw [← hX]
  exact h

end LocIota

section Loc

variable {D : D7} (Z : LocDat D) (p : PlF D)

theorem locX_eq {g2 g2' : Fin (D.R.rS + 1) → (VS D).V}
    (hX : Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) =
      Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc)) :
    (locH Z p).X (fun b => sF' Z p b • baseChange₂ D p (g2' b)) = (locH Z p).X (fun b => sF' Z p b • baseChange₂ D p (g2 b)) := by
  apply le_antisymm
  · unfold Loc.HermSp.X
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have hm : g2' a.castSucc ∈ Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc) := by
      rw [← hX]; exact Submodule.subset_span ⟨a, rfl⟩
    exact Submodule.smul_mem _ _ (bcP_mem_X Z p g2 (sF' Z p) (isUnit_sF' Z p) hm)
  · unfold Loc.HermSp.X
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have hm : g2 a.castSucc ∈ Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) := by
      rw [hX]; exact Submodule.subset_span ⟨a, rfl⟩
    exact Submodule.smul_mem _ _ (bcP_mem_X Z p g2' (sF' Z p) (isUnit_sF' Z p) hm)

theorem iotaEl_frameAct {Λ : Submodule (𝓞 D.host.E) (VS D).V} {f g1 h : Fin (D.R.rS + 1) → (VS D).V}
    {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) (hI : IotaEl Z p Λ f g1 (frameAct h ξ⁻¹) β) :
    IotaEl Z p Λ f g1 h β := by
  intro gg hgg
  exact iotaG_congr (locH Z p) (locX_eq Z p (Xs_frameAct_inv h ξ h1 h2)) (hI gg hgg)

end Loc

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.LprEx
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprExistB

section

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.LprEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}

theorem LprExistB_equiv {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : IsRowLat D F0 Λ) :
    Equivalence (Formalism.L2.SG.Corank.ScalRelD D u' F0 Λ) :=
  Formalism.L2.SG.Corank.scalarEquiv_of_G scalar_equiv_general u u' F0 Λ hΛ

theorem LprExistB_repFree : Formalism.L2.SG.Corank.ScalarRepFree D u u' :=
  scalar_rep_free D u u'

theorem scal_move {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : IsRowLat D F0 Λ)
    (x1 x2 y1 y2 : {x : Carrier (PD D Λ (lf D F0) u') // Gval (lf D F0) x.1 ≠ 0})
    (h1 : TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') x1.1 = TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') y1.1)
    (h2 : TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') x2.1 = TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') y2.1)
    (a : Formalism.L2.SG.Corank.ScalRelD D u' F0 Λ x1 x2) : Formalism.L2.SG.Corank.ScalRelD D u' F0 Λ y1 y2 := by
  have hEq := LprExistB_equiv (u := u) (u' := u') hΛ
  have hRF := LprExistB_repFree (D := D) (u := u) (u' := u') F0 Λ hΛ
  have r2 := (Formalism.L2.SG.Pf.double_coset_equivalence Λ (lf D F0) (PD D Λ (lf D F0) u') x2.1 y2.1).1 h2
  have a2 : Formalism.L2.SG.Corank.ScalRelD D u' F0 Λ x1 y2 := hRF x1 x2 y2 r2 a
  have r1 := (Formalism.L2.SG.Pf.double_coset_equivalence Λ (lf D F0) (PD D Λ (lf D F0) u') x1.1 y1.1).1 h1
  have a3 : Formalism.L2.SG.Corank.ScalRelD D u' F0 Λ y2 y1 := hRF y2 x1 y1 r1 (hEq.symm a2)
  exact hEq.symm a3

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.LprEx
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprExist

section

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LprEx

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem scal_rep (hrows : IsRowReps D F0 what₂) (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (hP : IsPartner γ Z F'')
    (hGr : Gval (lf D F0) (repF γ) ≠ 0) :
    ∃ β, IsPair γ.lam (lf D F0) (repF γ) F'' β (gS D) ∧ s0 γ.lam (lf D F0) (repF γ) F'' β D.R.k = 1 ∧
      IsScalar γ.lam (lf D F0) (repF γ) F'' β := by
  obtain ⟨hE, γ', ⟨pr, hp1, hp2, hps, hpsc⟩, h3, h3e⟩ := hP
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  have hGF : Gval (lf D F0) F'' ≠ 0 := hE.1.2.2
  obtain ⟨lam, mem, cls⟩ := γ
  obtain ⟨lam', mem', cls'⟩ := γ'
  obtain ⟨lp, mp, p1, p2, gp1, gp2, bp, ip⟩ := pr
  simp only [Formalism.L2.SG.Corank.Pair.pfst, Formalism.L2.SG.Corank.Pair.psnd] at hp1 hp2
  obtain ⟨rfl, hc1⟩ := hp1
  obtain ⟨rfl, hc2⟩ := hp2
  exact scal_move (hrows.1 _ mp) ⟨p1, gp1⟩ ⟨p2, gp2⟩ ⟨⟨repF _, h2⟩, hGr⟩ ⟨⟨F'', h3⟩, hGF⟩ h2e.symm h3e.symm
    ⟨bp, ip, hps, hpsc⟩

variable (Zd : LocDat D)



theorem lprExist_of (hI : Formalism.L2.SG.Pf.ScalarFramePf.IotaStep) : LprExist Zd u u' F0 what₂ := by
  intro hrows γ Z hC F'' hP p
  obtain ⟨w, hγ, -⟩ := hC
  have hR : IsRowLat D F0 γ.lam := hrows.1 γ.lam γ.mem
  have hF : FixedHyp D γ.lam (lf D F0) := hR.2.1
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  have hGr : Gval (lf D F0) (repF γ) ≠ 0 := gval_repF γ w hγ
  have hgenR : IsGeneric γ.lam (gS D) (lf D F0) (repF γ) := by
    obtain ⟨hgen, -⟩ := hγ.1
    obtain ⟨F', ⟨h1, h1e⟩, hF'⟩ := hgen
    have hrel := (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') ⟨F', h1⟩ ⟨repF γ, h2⟩).1
      (h1e.trans h2e.symm)
    exact (PI.TermAttrConst.UnitaryGroupMassFormula.genericity_constant_double_cosets D u u' F0 γ.lam hR ⟨F', h1⟩ ⟨repF γ, h2⟩ hrel).1 hF'
  have hE := hP.1
  obtain ⟨β, hPair, hs, hsc⟩ := scal_rep hrows γ Z F'' hP hGr
  have hT : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Formalism.L2.SG.Corank.tu_ne_zero u
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Formalism.L2.SG.Corank.tu_ne_zero u'
  have hG := Formalism.L2.SG.Pf.ScalarFramePf.gfacts_of γ.lam (lf D F0) (repF γ) F'' β hF h2.1 hE.1.1 h2.2.2.1
    hE.2.2.2.1.1 hPair hs hsc hGr hE.1.2.2 hT hT'
  have hIo := hI D Zd γ.lam (lf D F0) (repF γ) F'' β hF h2.1 hE.1.1 h2.2.2.1 hE.2.2.2.1.1 h2.2.1 hE.1.2.1 hPair
    hgenR hE.2.2.1 hs hsc hGr hE.1.2.2 hT hT' p
  have hξ := admissibility_witness_unitriangular γ.lam (lf D F0) F''
  have hG2 := gfacts_frameAct (admXi D γ.lam (lf D F0) F'') hξ.1 hξ.2 hG
  have hI2 := iotaEl_frameAct Zd p (admXi D γ.lam (lf D F0) F'') hξ.1 hξ.2 hIo
  obtain ⟨hId, hRe⟩ := Formalism.L2.SG.Pf.ScalarFramePf.identResp_lt Zd p γ.lam (frame (lf D F0)) _ (frame F'') β
    (Tu D u) (Tu D u') hG2 hI2
  exact ⟨Formalism.L2.SG.Pf.ScalarFramePf.phiP Zd p γ.lam (frame (lf D F0)) _ (frame F'') β hG2, hId, hRe.2.2.2.1,
    hRe.2.2.1, hRe.2.2.2.2⟩

theorem lprPart_of_iota (hI : Formalism.L2.SG.Pf.ScalarFramePf.IotaStep) : LprPart Zd u u' F0 what₂ :=
  lprPart_of' Zd (lprExist_of Zd hI)

end LprEx

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprClose

section

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem lprPart_holds : LprPart Zd u u' F0 what₂ :=
  LprEx.lprPart_of_iota Zd Formalism.L2.SG.Pf.iotaStep_holds

theorem fStarC_of_beta (hC : CtxP u u' F0 what₂) (hRat : BetaRat Zd u u' F0 what₂) (hInt : BetaInt Zd u u' F0 what₂) :
    FStarC Zd u u' F0 what₂ :=
  fStarC_of_leaves' Zd hC (lprPart_holds Zd) hRat hInt

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end
end
