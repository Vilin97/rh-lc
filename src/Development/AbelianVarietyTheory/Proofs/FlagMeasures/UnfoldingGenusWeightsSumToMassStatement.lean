module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivalenceComplementUnitaryOrbitLocalInnerDatumStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRowTermOfLocalCompletionsTermsStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrinciple
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrincipleStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermLatticeOverInnerDatumFgSpanStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLatticesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryComplementMovesLocalTermsWithDataStatement
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsComplementUnitaryMulActionLocalInnerDatumStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDatumEqOfSameLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalAutomorphismLocalExtensionMovesLatticesStatement
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitCountRowsDoubleCosetsInnerDatumClassStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalClassLatticesIffRationalClassLocalFramePStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SameRowDoubleCosetInnerDataOneRationalClassStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusFamilyCarriedByLatticeInLocalOrbits

section

@[expose] public section

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.GlueOrbit

variable {D : D7}

theorem finrank_loc (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h1 := D.R.m_even
  have h2 := D.R.two_le_m
  have h3 := D.R.m_add_three_le_k
  obtain ⟨c, hc⟩ := h1
  simp only [Ranks.r, Ranks.rS]
  omega

theorem localLattice_fg_and_span_eq_top (Z : LocDat D) (Λ : LV D) (h : Submodule.IsFullLattice D.host.E Λ) (p : PlF D) :
    (lattice₂ D Z.M p Λ).FG ∧ Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤ := by
  have hmap : Submodule.IsFullLattice D.host.E (LatLoc.cL Λ) := by
    refine { toIsLattice := LatLoc.isLattice_map _ _ h.toIsLattice, span_eq_top := ?_ }
    change Submodule.span D.host.E (((LatLoc.cE D).toLinearMap) '' (Λ : Set (VS D).V)) = ⊤
    rw [Submodule.span_image, h.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact (LatLoc.cE D).surjective
  have := (GlobalTheory.T.numberField_lattice_determined_by_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) (LatLoc.cL Λ) hmap).2.1 p
  rw [LatLoc.localLattice_eq]
  exact this

theorem img_one {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (L : Submodule M.L.O V) :
    LocNG.img (1 : V ≃ₗ[E] V) L = L := by
  ext x
  simp [LocNG.img]

theorem img_lattice {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (g : V ≃ₗ[E] V) (L : Submodule M.L.O V)
    (h : L.FG ∧ Submodule.span E (L : Set V) = ⊤) :
    (LocNG.img g L).FG ∧ Submodule.span E (LocNG.img g L : Set V) = ⊤ := by
  refine ⟨h.1.map _, ?_⟩
  unfold LocNG.img
  rw [Submodule.map_coe]
  have e1 : (⇑((g : V →ₗ[E] V).restrictScalars M.L.O) : V → V) = ⇑(g : V →ₗ[E] V) := rfl
  rw [e1, Submodule.span_image, h.2, Submodule.map_top, LinearMap.range_eq_top]
  exact g.surjective

theorem glue_local_orbits : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y y' : Dat Z FP), LocOver Λ y → InGen y y' → ∃ Λ', LocOver Λ' y' ∧ ∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p Λ' := by
  intro D X Y u u' F F' w _ _ Z FP _ hR Λ y y' ⟨hΛ, hτ⟩ ⟨hrel, hfin⟩
  have key : ∀ p, ∃ h ∈ (FP p).UW0, (y' p = y p → h = 1) ∧
      ∃ τ : Loc.Term (Vp D p) (Z.M p) D.R.rS, LocNG.IsTermOver (FP p) (y' p) τ ∧
        τ.abelian₂ = LocNG.img h (lattice₂ D Z.M p Λ) := by
    intro p
    obtain ⟨τ, hτ1, hτ2⟩ := hτ p
    by_cases hp : y' p = y p
    · exact ⟨1, one_mem _, fun _ => rfl, τ, hp ▸ hτ1, by rw [img_one, hτ2]⟩
    · obtain ⟨g, hg, hm⟩ := hrel p
      exact ⟨g, hg, fun h => absurd h hp, _,
        (GlobalTheory.T.unitaryComplement_moves_local_terms_with_data (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) (finrank_loc p) (hR p) g hg
          (y p) (y' p) τ hτ1 hm).1, by rw [← hτ2]⟩
  choose h hU h1 τ hτ1 hτ2 using key
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
  let p : PlF D := ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField D.host.F)⟩
  obtain ⟨t, ht, heq⟩ := hτ p
  have hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤ := by
    rw [← heq]
    exact (GlobalTheory.T.localTermLattice_over_innerDatum_fg_span D Z FP p (y p) t ht).2
  have hfull : Submodule.IsFullLattice D.host.E Λ := by
    let U := Submodule.span D.host.E (Λ : Set (VS D).V)
    let b := Module.finBasis D.host.E U
    let W := Submodule.span (D.s.atP p).Ep
      (Set.range fun i => baseChange₂ D p (b i : (VS D).V))
    have hW (x : U) : baseChange₂ D p (x : (VS D).V) ∈ W := by
      have hx := congrArg (fun y : U => baseChange₂ D p (y : (VS D).V)) (b.sum_repr x)
      change baseChange₂ D p (U.subtype (∑ i, b.repr x i • b i)) = _ at hx
      rw [map_sum, map_sum] at hx
      rw [← hx]
      exact W.sum_mem fun i _ => by
        rw [map_smul, baseChange_smul₂]
        exact W.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
    have htop : W = ⊤ := by
      apply top_le_iff.mp
      rw [← hspan, lattice₂, Submodule.span_span_of_tower]
      refine Submodule.span_le.2 ?_
      rintro y ⟨x, hx, heq⟩
      rw [← heq]
      exact hW ⟨x, Submodule.subset_span hx⟩
    refine { toIsLattice := hΛ, span_eq_top := Submodule.eq_of_le_of_finrank_le le_top ?_ }
    rw [finrank_top, Module.finrank_eq_card_basis (VS D).frame, Fintype.card_fin]
    simpa only [Module.finrank_fin_fun, Fintype.card_fin] using
      finrank_le_of_span_eq_top (show Submodule.span (D.s.atP p).Ep _ = ⊤ from htop)
  obtain ⟨Λ', hΛ', hp⟩ := (GlobalTheory.T.hermitianLattice_local_global_principle D Z).2 Λ hfull (fun p => LocNG.img (h p) (lattice₂ D Z.M p Λ))
    (fun p => by
      obtain ⟨t, ht, heq⟩ := hτ p
      apply img_lattice
      rw [← heq]
      exact GlobalTheory.T.localTermLattice_over_innerDatum_fg_span D Z FP p (y p) t ht)
    (hfin.subset fun p hp hc => hp (by simp only [h1 p hc, img_one]))
  exact ⟨Λ', ⟨hΛ', fun p => ⟨τ p, hτ1 p, (hτ2 p).trans (hp p).symm⟩⟩, fun p => ⟨h p, hU p, (hp p).symm⟩⟩

end GlobalTheory.Unfold.GlueOrbit
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusFamilyCarriedByLatticeInLocalOrbitsStatement

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.genusFamily_carried_by_lattice_in_localOrbits : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y y' : Dat Z FP), LocOver Λ y → InGen y y' → ∃ Λ', LocOver Λ' y' ∧ ∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p Λ' := by
  first | exact @GlobalTheory.Unfold.GlueOrbit.glue_local_orbits | exact GlobalTheory.Unfold.GlueOrbit.glue_local_orbits | (intros; apply GlobalTheory.Unfold.GlueOrbit.glue_local_orbits <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusStableUnderRationalComplementGroup

section

@[expose] public section

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GenusStab

theorem finrank_Vp_k (D : D7) (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h2 := D.R.two_le_m
  obtain ⟨c, hc⟩ := D.R.m_even
  simp only [Ranks.r, Ranks.rS]
  omega

theorem inGen_of_gRel : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (d y y' : Dat Z FP), LocOver Λ y → InGen d y → GRel F F' y y' → InGen d y' := by
  intro D X Y u u' F F' w hw hG Z FP hB hRel Λ d y y' hov hgen hgr
  obtain ⟨hext, hUW, -, hmove⟩ := GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hw hG Z FP hB hRel
  obtain ⟨h, hh, hmv⟩ := hgr
  obtain ⟨y'', hov'', hmv''⟩ := hmove h hh Λ y hov
  have hact := fun p => GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
    (finrank_Vp_k D p) (hRel p)
  choose act hiff _ using hact
  have heq : ∀ p, y' p = y'' p := by
    intro p
    obtain ⟨g1, he1, hm1⟩ := hmv p
    obtain ⟨g2, he2, hm2⟩ := hmv'' p
    obtain rfl : g1 = g2 := (hext h p).unique he1 he2
    have hg : g1 ∈ (FP p).UW0 := hUW h hh p g1 he1
    have a1 := ((hiff p) ⟨g1, hg⟩ (y p) (y' p)).1 hm1
    have a2 := ((hiff p) ⟨g1, hg⟩ (y p) (y'' p)).1 hm2
    rw [← a1, ← a2]
  refine ⟨fun p => ?_, ?_⟩
  · obtain ⟨g0, hg0, hm0⟩ := hgen.1 p
    obtain ⟨g1, he1, hm1⟩ := hmv p
    have hg1 : g1 ∈ (FP p).UW0 := hUW h hh p g1 he1
    have a0 := ((hiff p) ⟨g0, hg0⟩ (d p) (y p)).1 hm0
    have a1 := ((hiff p) ⟨g1, hg1⟩ (y p) (y' p)).1 hm1
    refine ⟨g1 * g0, mul_mem hg1 hg0, ((hiff p) ⟨g1 * g0, mul_mem hg1 hg0⟩ (d p) (y' p)).2 ?_⟩
    letI := act p
    let a : (FP p).UW0 := ⟨g1, hg1⟩
    let b : (FP p).UW0 := ⟨g0, hg0⟩
    have hm : (a * b) • d p = a • (b • d p) := mul_smul a b (d p)
    change (a * b) • d p = y' p
    rw [hm]
    change a • (act p).smul b (d p) = y' p
    rw [a0]
    exact a1
  · have full_of_over (L : LV D) (z : Dat Z FP) (hz : LocOver L z) :
        Submodule.IsFullLattice D.host.E L := by
      obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
      let p : PlF D := ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField D.host.F)⟩
      obtain ⟨t, ht, heq⟩ := hz.2 p
      have hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p L : Set (Vp D p)) = ⊤ := by
        rw [← heq]
        exact (GlobalTheory.T.localTermLattice_over_innerDatum_fg_span D Z FP p (z p) t ht).2
      let U := Submodule.span D.host.E (L : Set (VS D).V)
      let b := Module.finBasis D.host.E U
      let W := Submodule.span (D.s.atP p).Ep
        (Set.range fun i => baseChange₂ D p (b i : (VS D).V))
      have hW (x : U) : baseChange₂ D p (x : (VS D).V) ∈ W := by
        have hx := congrArg (fun y : U => baseChange₂ D p (y : (VS D).V)) (b.sum_repr x)
        change baseChange₂ D p (U.subtype (∑ i, b.repr x i • b i)) = _ at hx
        rw [map_sum, map_sum] at hx
        rw [← hx]
        exact W.sum_mem fun i _ => by
          rw [map_smul, baseChange_smul₂]
          exact W.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
      have htop : W = ⊤ := by
        apply top_le_iff.mp
        rw [← hspan, lattice₂, Submodule.span_span_of_tower]
        refine Submodule.span_le.2 ?_
        rintro y ⟨x, hx, heq⟩
        rw [← heq]
        exact hW ⟨x, Submodule.subset_span hx⟩
      refine { toIsLattice := hz.1, span_eq_top := Submodule.eq_of_le_of_finrank_le le_top ?_ }
      rw [finrank_top, Module.finrank_eq_card_basis (VS D).frame, Fintype.card_fin]
      simpa only [Module.finrank_fin_fun, Fintype.card_fin] using
        finrank_le_of_span_eq_top (show Submodule.span (D.s.atP p).Ep _ = ⊤ from htop)
    have hfin := ((GlobalTheory.T.hermitianLattice_local_global_principle D Z).1 Λ (Formalism.HermitianLatticesTheory.gmap h Λ) (full_of_over Λ y hov) (full_of_over _ y'' hov'')).1
    refine (hfin.union hgen.2).subset fun p hp => ?_
    by_cases hyd : y p = d p
    · left
      intro hl
      apply hp
      rw [heq p, ← hyd]
      obtain ⟨τ, hτ, hL⟩ := hov.2 p
      obtain ⟨τ'', hτ'', hL''⟩ := hov''.2 p
      have hlam : τ''.abelian₂ = τ.abelian₂ := by rw [hL'', hL]; exact hl.symm
      have key := GlobalTheory.T.hermitianDatum_eq_of_same_lattice (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
        (finrank_Vp_k D p) (hRel p) (y'' p) (y p) τ'' τ hτ'' hτ
      exact key hlam
    · right
      exact hyd

end GlobalTheory.GenusStab
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusStableUnderRationalComplementGroupStatement

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.genus_stable_under_rationalComplementGroup : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (d y y' : Dat Z FP), LocOver Λ y → InGen d y → GRel F F' y y' → InGen d y' := by
  first | exact @GlobalTheory.GenusStab.inGen_of_gRel | exact GlobalTheory.GenusStab.inGen_of_gRel | (intros; apply GlobalTheory.GenusStab.inGen_of_gRel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnfoldingGenusWeightsSumToMass

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.SumK

theorem inGen_symm_of {D : D7} {Z : LocDat D} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS}
    (hE : ∀ p, Equivalence (LocNG.Datum.Rel (P := FP p))) {d y y' : Dat Z FP}
    (h : InGen d y) (h' : InGen d y') : InGen y y' := by
  refine ⟨fun p => (hE p).trans ((hE p).symm (h.1 p)) (h'.1 p), ?_⟩
  apply (h.2.union h'.2).subset
  intro p hp
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  exact hp (by rw [hc.1, hc.2])

theorem weights_add_up_to_mass_of
    (hRelEqv : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D), Equivalence (LocNG.Datum.Rel (P := FP p)))
    (hInv : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (d y y' : Dat Z FP), LocOver Λ y → InGen d y → GRel F F' y y' → InGen d y') :
    ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ TS : Set (TauC Y u u'), LocClosed F F' Z FP TS → ∀ (t₀ : TauC Y u u') (Λ₀ : LV D) (y₀ d : Dat Z FP), t₀ ∈ TS → TG F F' t₀ Λ₀ → LocOver Λ₀ y₀ → InGen d y₀ → ∀ K, K = {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat Z FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ} → ∀ ω : K → ℝ, (∀ κ : K, ∀ t : TauC Y u u', key t = κ.1 → ω κ = wt t ^ 2) → ∑' κ : K, ENNReal.ofReal (ω κ) = massA F F' d := by
  intro D X Y u u' F F' w hw hG Z FP hB hR TS hTS t₀ Λ₀ y₀ d ht₀ hTG₀ hLO₀ hIG₀ K hK ω hω
  subst hK
  obtain ⟨hEq, -, hRel⟩ := GlobalTheory.T.rationalClass_lattices_iff_rationalClass_localFramePairs D X Y u u' F F' w hw hG Z FP hB hR
  have hQ : ∀ y y' : Dat Z FP, (Quot.mk (GRel (Z := Z) (FP := FP) F F') y) = Quot.mk _ y' ↔ GRel F F' y y' :=
    fun y y' => ⟨fun h => hEq.eqvGen_iff.1 (Quot.eqvGen_exact h), Quot.sound⟩
  have hout : ∀ o : Quot (GRel (Z := Z) (FP := FP) F F'), ∀ y, Quot.mk _ y = o → GRel F F' o.out y := by
    intro o y h
    exact (hQ _ _).1 (by rw [h, Quot.out_eq])

  have hex : ∀ κ : {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat Z FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ},
      ∃ y : Dat Z FP, ∃ t ∈ TS, ∃ Λ : LV D, TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ.1 := by
    rintro ⟨κ, t, ht, Λ, y, h1, h2, h3, h4⟩
    exact ⟨y, t, ht, Λ, h1, h2, h3, h4⟩
  choose yOf hyOf using hex
  set φ := fun κ => (Quot.mk (GRel (Z := Z) (FP := FP) F F') (yOf κ)) with hφ
  have hwd : ∀ (t t' : TauC Y u u') (Λ Λ' : LV D) (y y' : Dat Z FP), TG F F' t Λ → TG F F' t' Λ' →
      LocOver Λ y → LocOver Λ' y' → key t = key t' → GRel F F' y y' := fun t t' Λ Λ' y y' h1 h2 h3 h4 h5 =>
    ((hRel Λ Λ' y y' h3 h4).1).1 (GlobalTheory.T.same_row_doubleCoset_inner_data_one_rational_class D X Y u u' F F' w hw hG t t' Λ Λ' h1 h2 h5)
  have hImg : ∀ κ, InGen d (φ κ).out := by
    intro κ
    obtain ⟨t, -, Λ, h1, h2, h3, -⟩ := hyOf κ
    exact hInv D X Y u u' F F' w hw hG Z FP hB hR Λ d (yOf κ) _ h2 h3 (hEq.symm (hout _ _ rfl))
  unfold massA
  rw [← ENNReal.tsum_fiberwise _ φ]
  refine tsum_congr fun o => ?_
  by_cases ho : InGen d o.out
  · rw [if_pos ho]
    have hIG01 : InGen y₀ o.out := inGen_symm_of (hRelEqv D Z FP) hIG₀ ho
    obtain ⟨Λ₁, hLO₁, hloc⟩ := GlobalTheory.T.genusFamily_carried_by_lattice_in_localOrbits D X Y u u' F F' w hw hG Z FP hB hR Λ₀ y₀ o.out hLO₀ hIG01
    obtain ⟨t₁, hTG₁⟩ := GlobalTheory.T.exists_rowTerm_of_local_completions_terms D X Y u u' F F' w hw hG Z FP hB hR Λ₁ o.out hLO₁
    have ht₁ : t₁ ∈ TS := hTS t₀ t₁ Λ₀ Λ₁ hTG₀ hTG₁ hloc ht₀
    obtain ⟨-, hcarry, hwt, hmass⟩ := GlobalTheory.T.orbitCount_rows_doubleCosets_innerDatum_class D X Y u u' F F' w hw hG t₁ Λ₁ hTG₁ _ rfl
    have hRefl : LRel F F' Λ₁ Λ₁ := ((hRel Λ₁ Λ₁ o.out o.out hLO₁ hLO₁).1).2 (hEq.refl _)
    have hStab : stabL F F' Λ₁ = stabY F F' o.out := (hRel Λ₁ Λ₁ o.out o.out hLO₁ hLO₁).2

    have hfib : Subtype.val '' (φ ⁻¹' {o}) =
        {κ | ∃ (t : TauC Y u u') (Λ' : LV D), TG F F' t Λ' ∧ LRel F F' Λ₁ Λ' ∧ key t = κ} := by
      ext κ
      constructor
      · rintro ⟨b, hb, rfl⟩
        obtain ⟨t, -, Λ, h1, h2, -, h4⟩ := hyOf b
        have hb' : φ b = o := hb
        refine ⟨t, Λ, h1, ((hRel Λ₁ Λ o.out (yOf b) hLO₁ h2).1).2 (hout o _ hb'), h4⟩
      · rintro hκ
        obtain ⟨t, hTG, hkey⟩ := hcarry κ hκ
        have htS : t ∈ TS := hTS t₁ t Λ₁ Λ₁ hTG₁ hTG
          (fun p => ⟨1, Subgroup.one_mem _, by
            simp [LocNG.img]⟩) ht₁
        have hmem : κ ∈ {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat Z FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ} :=
          ⟨t, htS, Λ₁, o.out, hTG, hLO₁, ho, hkey⟩
        refine ⟨⟨κ, hmem⟩, ?_, rfl⟩
        show φ ⟨κ, hmem⟩ = o
        obtain ⟨t', -, Λ', h1, h2, -, h4⟩ := hyOf ⟨κ, hmem⟩
        rw [hφ]
        simp only
        rw [← Quot.out_eq o]
        exact Quot.sound (hwd t' t Λ' Λ₁ _ _ h1 hTG h2 hLO₁ (h4.trans hkey.symm))
    have hconst : ∀ b : φ ⁻¹' {o}, ENNReal.ofReal (ω b.1) = ENNReal.ofReal (wt t₁ ^ 2) := by
      intro b
      have hb : b.1.1 ∈ Subtype.val '' (φ ⁻¹' {o}) := ⟨b.1, b.2, rfl⟩
      rw [hfib] at hb
      obtain ⟨t, hTG, hkey⟩ := hcarry _ hb
      rw [hω b.1 t hkey, hwt t Λ₁ hTG hRefl]
    rw [tsum_congr hconst, ENNReal.tsum_set_const, ← Subtype.val_injective.encard_image, hfib, hmass, hStab]
  · rw [if_neg ho]
    refine ENNReal.tsum_eq_zero.2 fun b => (ho ?_).elim
    have hb : φ b.1 = o := b.2
    rw [← hb]
    exact hImg b.1

theorem weights_add_up_to_mass : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ TS : Set (TauC Y u u'), LocClosed F F' Z FP TS → ∀ (t₀ : TauC Y u u') (Λ₀ : LV D) (y₀ d : Dat Z FP), t₀ ∈ TS → TG F F' t₀ Λ₀ → LocOver Λ₀ y₀ → InGen d y₀ → ∀ K, K = {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat Z FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ} → ∀ ω : K → ℝ, (∀ κ : K, ∀ t : TauC Y u u', key t = κ.1 → ω κ = wt t ^ 2) → ∑' κ : K, ENNReal.ofReal (ω κ) = massA F F' d :=
  weights_add_up_to_mass_of GlobalTheory.T.equivalence_complementUnitaryOrbit_localInnerDatum_at_place GlobalTheory.T.genus_stable_under_rationalComplementGroup

end GlobalTheory.Unfold.SumK
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnfoldingGenusWeightsSumToMassStatement

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unfolding_genus_weights_sum_to_mass : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ TS : Set (TauC Y u u'), LocClosed F F' Z FP TS → ∀ (t₀ : TauC Y u u') (Λ₀ : LV D) (y₀ d : Dat Z FP), t₀ ∈ TS → TG F F' t₀ Λ₀ → LocOver Λ₀ y₀ → InGen d y₀ → ∀ K, K = {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat Z FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ} → ∀ ω : K → ℝ, (∀ κ : K, ∀ t : TauC Y u u', key t = κ.1 → ω κ = wt t ^ 2) → ∑' κ : K, ENNReal.ofReal (ω κ) = massA F F' d := by
  first | exact @GlobalTheory.Unfold.SumK.weights_add_up_to_mass | exact GlobalTheory.Unfold.SumK.weights_add_up_to_mass | (intros; apply GlobalTheory.Unfold.SumK.weights_add_up_to_mass <;> assumption)
end
end
