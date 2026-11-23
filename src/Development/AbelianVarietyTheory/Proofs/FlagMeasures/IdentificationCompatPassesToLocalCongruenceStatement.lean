module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalVectorCongruentLocalOrthogonal
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerOneModGAtPlaceZeroElsewhereStatement
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.T2SpaceOfNonarchimedeanLocalField
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalGlobalCongruenceLatticeTypedPlaceStatement
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalVectorCongruentLocalOrthogonalStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_global_vector_congruent_local_orthogonal : ∀ (D : D7) (Z : LocDat D) (p : PlF D), (∀ c ∈ (D.s.atP p).O, ∃ a : 𝓞 D.host.E, ∃ o ∈ (D.s.atP p).O, c = (D.s.atP p).ιE (a : D.host.E) + (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o) → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V), Submodule.IsLattice D.host.E Λ → ∀ {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T), ∀ x ∈ lattice₂ D Z.M p Λ, x ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame F))) → ∃ l ∈ Lrep Λ F, x - baseChange₂ D p l ∈ (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Formalism.MainNotions.S.LocNG.theta (Z.M p))) (lattice₂ D Z.M p Λ) := by
  first | exact @GlobalTheory.LocApprox.approx | exact GlobalTheory.LocApprox.approx | (intros; apply GlobalTheory.LocApprox.approx <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegersDenseLocalIntegersModG

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.IotaDense

theorem iota_dense : ∀ (D : D7) (p : PlF D), ∀ c ∈ (D.s.atP p).O, ∃ a : 𝓞 D.host.E, ∃ o ∈ (D.s.atP p).O,
    c = (D.s.atP p).ιE (a : D.host.E) + (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o := by
  intro D p c hc
  obtain ⟨hR, -, -, -, hO, -, -, -, hunit, hcl⟩ := GlobalTheory.LocAtTopology.locAt_topology D.sp.cm D.conjF
    (fun x => by rw [D.conjF_eq, Formalism.BasicNotions.Examples₂.star_eq_conj]) p (D.s.atP p)
  have hg : ((gS D : ℕ) : D.host.E) ≠ 0 := by
    have : gS D ≠ 0 := by
      unfold gS
      exact mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
    exact_mod_cast this
  obtain ⟨w, hw⟩ := hunit _ hg
  set S : Set (D.s.atP p).Ep := (fun z => ((w⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) * (c - z)) ⁻¹' ((D.s.atP p).O : Set _)
    with hSdef
  have hSo : IsOpen S := hO.preimage (continuous_const.mul (continuous_const.sub continuous_id))
  have hcS : c ∈ S := by
    show _ * (c - c) ∈ (D.s.atP p).O
    rw [sub_self, mul_zero]; exact zero_mem _
  have hcc : c ∈ closure (Set.range fun x : 𝓞 D.host.E => (D.s.atP p).ιE (x : D.host.E)) := by
    rw [hcl]; exact hc
  obtain ⟨z, hzS, a, rfl⟩ := mem_closure_iff.1 hcc S hSo hcS
  refine ⟨a, _, hzS, ?_⟩
  show c = _ + _ * (((w⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) * (c - _))
  rw [← hw, ← mul_assoc, Units.mul_inv, one_mul]
  ring

end GlobalTheory.IotaDense
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegersDenseLocalIntegersModGStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integers_dense_localIntegers_mod_g : ∀ (D : D7) (p : PlF D), ∀ c ∈ (D.s.atP p).O, ∃ a : 𝓞 D.host.E, ∃ o ∈ (D.s.atP p).O, c = (D.s.atP p).ιE (a : D.host.E) + (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o := by
  first | exact @GlobalTheory.IotaDense.iota_dense | exact GlobalTheory.IotaDense.iota_dense | (intros; apply GlobalTheory.IotaDense.iota_dense <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdentificationCompatPassesToLocalCongruence

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IotaLoc

section Gen

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {r : ℕ}
  (H : HermSp M V) (Λ : Submodule M.L.O V) (f f' : Fin (r + 1) → V)

theorem cong_add {v w : V} (hv : Cong H Λ f f' v) (hw : Cong H Λ f f' w) : Cong H Λ f f' (v + w) := by
  obtain ⟨a, ha, b, hb, c, hc, hbX, hcX, rfl⟩ := hv
  obtain ⟨a', ha', b', hb', c', hc', hbX', hcX', rfl⟩ := hw
  exact ⟨a + a', add_mem ha ha', b + b', add_mem hb hb', c + c', add_mem hc hc', add_mem hbX hbX',
    add_mem hcX hcX', by abel⟩

theorem cong_neg {v : V} (hv : Cong H Λ f f' v) : Cong H Λ f f' (-v) := by
  obtain ⟨a, ha, b, hb, c, hc, hbX, hcX, rfl⟩ := hv
  exact ⟨-a, neg_mem ha, -b, neg_mem hb, -c, neg_mem hc, neg_mem hbX, neg_mem hcX, by abel⟩

theorem cong_of_mem {v : V} (hv : v ∈ H.smulLat (algebraMap F E (theta M)) Λ) : Cong H Λ f f' v :=
  ⟨v, hv, 0, zero_mem _, 0, zero_mem _, zero_mem _, zero_mem _, by simp⟩

theorem cong_iff_of_sub {v w : V} (h : v - w ∈ H.smulLat (algebraMap F E (theta M)) Λ) :
    Cong H Λ f f' v ↔ Cong H Λ f f' w := by
  constructor
  · intro hv
    have := cong_add H Λ f f' hv (cong_neg H Λ f f' (cong_of_mem H Λ f f' h))
    rwa [show v + -(v - w) = w by abel] at this
  · intro hw
    have := cong_add H Λ f f' hw (cong_of_mem H Λ f f' h)
    rwa [show w + (v - w) = v by abel] at this

end Gen

section Glob

variable {D : D7}

theorem ext_latP (Z : LocDat D) (p : PlF D) {β : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p} (hg : Ext p β g) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hβΛ : Formalism.HermitianLatticesTheory.gmap β Λ = Λ) {v : Vp D p} (hv : v ∈ lattice₂ D Z.M p Λ) : g v ∈ lattice₂ D Z.M p Λ := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨y, hy, rfl⟩ := hv
    rw [hg y]
    refine Submodule.subset_span ⟨β y, ?_, rfl⟩
    rw [← hβΛ]
    exact Submodule.mem_map_of_mem hy
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul o v _ hv =>
    have e : g (o • v) = o • g v := by rw [Subring.smul_def, Subring.smul_def, map_smul]
    rw [e]; exact Submodule.smul_mem _ o hv

theorem ext_smulLat (Z : LocDat D) (p : PlF D) {β : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p} (hg : Ext p β g) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hβΛ : Formalism.HermitianLatticesTheory.gmap β Λ = Λ) (c : (D.s.atP p).Ep) {v : Vp D p}
    (hv : v ∈ (locH Z p).smulLat c (lattice₂ D Z.M p Λ)) : g v ∈ (locH Z p).smulLat c (lattice₂ D Z.M p Λ) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w, hw, rfl⟩ := hv
    show g (c • w) ∈ _
    rw [map_smul]
    exact Submodule.subset_span ⟨g w, ext_latP Z p hg hβΛ hw, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul o v _ hv =>
    have e : g (o • v) = o • g v := by rw [Subring.smul_def, Subring.smul_def, map_smul]
    rw [e]; exact Submodule.smul_mem _ o hv

end Glob

theorem iota_typed : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), PD D Λ (lf D F0) u' F₁ → PD D Λ (lf D F0) u' F₂ → ∀ β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, Formalism.HermitianLatticesTheory.gmap β Λ = Λ → (∀ a, frame F₂ a = β (frame F₁ a)) → IotaCompat Λ (lf D F0) F₁ F₂ β (gS D) → ∀ (p : PlF D) (g), Ext p β g → (Z.M p).split ≠ none → ∀ x' ∈ lattice₂ D Z.M p Λ, ∀ x ∈ lattice₂ D Z.M p Λ, x' ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame F₁))) → x ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame (lf D F0)))) → (Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₁)) (x - x') ↔ Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₂)) (x - g x')) := by
  intro D Z u u' F0 Λ hR F₁ F₂ _ _ β _ hβΛ _ hIota p g hg hsp x' hx'Λ x hxΛ hx' hx
  have hΛ : Submodule.IsLattice D.host.E Λ := hR.2.1.1
  have hLD := GlobalTheory.T.integers_dense_localIntegers_mod_g D p
  obtain ⟨l, hl, hxl⟩ := GlobalTheory.T.exists_global_vector_congruent_local_orthogonal D Z p hLD Λ hΛ (lf D F0) x hxΛ hx
  obtain ⟨l', hl', hxl'⟩ := GlobalTheory.T.exists_global_vector_congruent_local_orthogonal D Z p hLD Λ hΛ F₁ x' hx'Λ hx'
  obtain ⟨a, ha1, ha2⟩ := GlobalTheory.T.exists_integer_one_mod_g_at_place_zero_elsewhere D p
  have hlΛ : l ∈ Λ := (Submodule.mem_inf.1 hl).1
  have hl'Λ : l' ∈ Λ := (Submodule.mem_inf.1 hl').1
  have hβl' : β l' ∈ Λ := by rw [← hβΛ]; exact Submodule.mem_map_of_mem hl'Λ
  have e1 : Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₁)) (x - x') ↔
      Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₁)) (baseChange₂ D p (l - l')) := by
    apply cong_iff_of_sub
    have e : x - x' - baseChange₂ D p (l - l') = (x - baseChange₂ D p l) - (x' - baseChange₂ D p l') := by rw [map_sub]; abel
    rw [e]; exact sub_mem hxl hxl'
  have e2 : Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₂)) (x - g x') ↔
      Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₂)) (baseChange₂ D p (l - β l')) := by
    apply cong_iff_of_sub
    have e : x - g x' - baseChange₂ D p (l - β l') = (x - baseChange₂ D p l) - g (x' - baseChange₂ D p l') := by
      rw [map_sub, map_sub, hg l']; abel
    rw [e]; exact sub_mem hxl (ext_smulLat Z p hg hβΛ _ hxl')
  rw [e1, e2, ← GlobalTheory.T.local_global_congruence_lattice_typed_place D Z p hsp a ha1 ha2 Λ hΛ (lf D F0) F₁ (l - l') (sub_mem hlΛ hl'Λ), ← GlobalTheory.T.local_global_congruence_lattice_typed_place D Z p hsp a ha1 ha2 Λ hΛ (lf D F0) F₂ (l - β l') (sub_mem hlΛ hβl')]
  have hal : a • l ∈ Lrep Λ (lf D F0) := Submodule.smul_mem _ a hl
  have hal' : a • l' ∈ Lrep Λ F₁ := Submodule.smul_mem _ a hl'
  have h := hIota (a • l') hal' (a • l) hal
  have e3 : β (a • l') = a • β l' := by
    rw [← algebraMap_smul D.host.E a l', LinearEquiv.map_smul, algebraMap_smul]
  rw [e3] at h
  rw [smul_sub, smul_sub]
  exact h

end GlobalTheory.IotaLoc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdentificationCompatPassesToLocalCongruenceStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.identificationCompat_passes_to_local_congruence : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), PD D Λ (lf D F0) u' F₁ → PD D Λ (lf D F0) u' F₂ → ∀ β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, Formalism.HermitianLatticesTheory.gmap β Λ = Λ → (∀ a, frame F₂ a = β (frame F₁ a)) → IotaCompat Λ (lf D F0) F₁ F₂ β (gS D) → ∀ (p : PlF D) (g), Ext p β g → (Z.M p).split ≠ none → ∀ x' ∈ lattice₂ D Z.M p Λ, ∀ x ∈ lattice₂ D Z.M p Λ, x' ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame F₁))) → x ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame (lf D F0)))) → (Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₁)) (x - x') ↔ Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₂)) (x - g x')) := by
  first | exact @GlobalTheory.IotaLoc.iota_typed | exact GlobalTheory.IotaLoc.iota_typed | (intros; apply GlobalTheory.IotaLoc.iota_typed <;> assumption)
end
end
