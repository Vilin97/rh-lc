module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalIndex
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FamTrace.RedAt
section Split
variable {D : D7} {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : GlobalTheory.FinPl.SplitPt D K) {PP : HeightOneSpectrum (𝓞 D.host.E)} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP)
include hq
end Split
end GlobalTheory.FamTrace.RedAt
namespace GlobalTheory.FamTrace.RedAt
set_option maxHeartbeats 1000000 in
theorem inJ_red_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Gi : Formalism.MainNotions.G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L} {Gl : Formalism.MainNotions.G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {cX : ExtraC} {ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (Formalism.L2.Forms.gramN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F), GlobalTheory.AdForm.finM ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X 0) (Formalism.L2.Forms.rankN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) 0 (Nat.zero_le _)) κ = y.1.1 → ∀ (i : Fin a.n) (v : HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)) (i0 : Fin 2) (h : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g i0 : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∈ v.asIdeal), (a.G i).q.v = v → (∀ r c : Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X 0).rank, ((mt ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X 0) κ).map (a.G i).q.pr) r c ∈ 𝒪[(a.G i).k] ∧ (c ≤ r → valuation (a.G i).k (((mt ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X 0) κ).map (a.G i).q.pr) r c - (1 : Matrix (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X 0).rank) (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X 0).rank) (a.G i).k) r c) < 1)) → Formalism.L2.Forms.InJ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.k (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.t ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N 0) false (Formalism.L2.Forms.redM (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F v ((_root_.GlobalTheory.MiTop.formsAtZero W u).gl.mat i0 v h 1 (Formalism.UG.bc (Formalism.UG.prV (E := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) v) y.1))) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hat row col hc κ hκ y hy i v i0 h hv hM
  have hstd := hA.tr.std.some u
  obtain ⟨w, hw, ρ, hu, hres⟩ := GlobalTheory.Mem.Col2.TC.GLev0.exists_w (_root_.GlobalTheory.MiTop.formsAtZero W u).gl hstd.gl.piG i0 v h
  have hid := (ha.tie row col).2.idem i
  have hPg : (a.pl i).1 ∈ (B.primes X).vGs := (hA.lev.2.1 _).1 (a.pl i).2
  have hwe : w = (a.pl i).1 := GlobalTheory.Mem.Col2.TC.GLev0.vGs_inj (X := X) hPg
    (GlobalTheory.Mem.Col2.TC.GLev0.mem_vGs.2 ⟨i0, hw⟩) (hu.trans (hv.symm.trans hid.2))
  subst hwe
  have hn : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N 0 = (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.k := by simp [Ranks.N]
  have hr := Formalism.L2.Forms.rankN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) 0 (Nat.zero_le _)
  have key : ∀ r c : Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N 0), c ≤ r →
      Formalism.L2.Forms.redM (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F v ((_root_.GlobalTheory.MiTop.formsAtZero W u).gl.mat i0 v h 1 (Formalism.UG.bc (Formalism.UG.prV (E := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) v) y.1)) r c =
        if r = c then 1 else 0 := by
    intro r c hcr
    obtain ⟨r', rfl⟩ : ∃ r', r = finCongr hr r' := ⟨(finCongr hr).symm r, by simp⟩
    obtain ⟨c', rfl⟩ : ∃ c', c = finCongr hr c' := ⟨(finCongr hr).symm c, by simp⟩
    have hcr' : c' ≤ r' := hcr
    have hsm := (hM r' c').2 hcr'
    have hinj : (finCongr hr r' = finCongr hr c') ↔ r' = c' := (finCongr hr).injective.eq_iff
    have e1 : (a.G i).q.pr (incA (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (((if r' = c' then 1 else 0 : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)) =
        (1 : Matrix (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X 0).rank) (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X 0).rank) (a.G i).k) r' c' := by
      rw [Matrix.one_apply]
      split_ifs <;> simp
    have hR := hasRes_of_pr (a.G i).q hid.1 (z := mt ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X 0) κ r' c') (if r' = c' then 1 else 0) (by
      rw [e1]
      exact hsm)
    have hyrc : y.1.1 (finCongr hr r') (finCongr hr c') = toEAf (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (mt ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X 0) κ r' c') := by
      rw [← hy]
      rfl
    rw [← hyrc] at hR
    obtain ⟨hh, e⟩ := hres _ _ hR
    rw [GlobalTheory.Mem.Col2.TC.GLev0.mat_one]
    unfold Formalism.L2.Forms.redM
    refine (dif_pos hh).trans (e.trans ?_)
    by_cases hrc : r' = c'
    · subst hrc
      rw [if_pos rfl, if_pos rfl, map_one]
      exact map_one ρ
    · rw [if_neg hrc, if_neg (fun e => hrc (hinj.1 e)), map_zero]
      exact map_zero ρ
  have hlt : ∀ x : Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N 0), (x : ℕ) < (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.k := fun x => hn ▸ x.2
  have hb : ∀ x : Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N 0), Formalism.L2.Forms.blkOf (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.k (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.t x = x :=
    fun x => if_pos (hlt x)
  refine ⟨fun x z hxz => ?_, fun x _ => ?_, fun x z hz => absurd hz (ne_of_lt z.2), fun h' => absurd h' (by simp)⟩
  · rw [hb, hb] at hxz
    rw [key x z (le_of_lt (show z < x from hxz)), if_neg (fun e => by subst e; exact lt_irrefl _ hxz)]
  · rw [key x x le_rfl, if_pos rfl]
end GlobalTheory.FamTrace.RedAt
end
