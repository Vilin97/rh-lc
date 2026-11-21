module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MiddleStepOneLevelProjectionEqChartProjectionStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostPrimesOverLevelPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRelationClassesCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicConjugateCharacterStandardFormsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalEqOfClassesRelatedAtPlaceStatement

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt


set_option maxHeartbeats 4000000 in
theorem dnCl_of_tie {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G))
    (F : ∀ u, FormsTiedSym (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u (H.Ch u) (H.chOf u))
    (hS : ∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) (hC : CarH H F) (u) (i : ℕ) (hi : i ≤ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m) (v)
    (c : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).mem u).C.cls i)
    (g : Module.Dual (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).mem u).A.Fv v) (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).fm u).lk i v c))
    (γ₀ : UJ (sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →+* (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (gramN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi))
    (hAd : AdC (F u) i hi c (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).fm u).dn i v c g) γ₀.1 ((F u).atT.eV v).1)
    (hloc : Formalism.HermitianLatticesTheory.localization₂ ((F u).atT.Pv v) (Formalism.L2.Forms.mulLat γ₀.1.1
        (Formalism.L2.Forms.Ld (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u i hi (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).fm u).dn i v c g))) =
      Formalism.HermitianLatticesTheory.localization₂ ((F u).atT.Pv v) (clsCrd (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u i hi c))
    (hfv : ∀ (x : Formalism.L2.Forms.Ld (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u i hi (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).fm u).dn i v c g))
      (hx : γ₀.1.1 *ᵥ x.1 ∈ Formalism.L2.Forms.Lk (F u).atT i hi v c),
      ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).fm u).fv i v _ (((F u).lv i hi).pr v _ x) = g (((F u).lv i hi).prk v c ⟨_, hx⟩)) :
    DnCl (F u).atT (F u).lv i v c g (gx i hi γ₀) ∧
      AdOf H u i c (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).fm u).dn i v c g) (gx i hi γ₀) v := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, GlobalTheory.T.adelic_relation_classes_coordinates I hOk hP l Z H F hS hC u i hi v c _ γ₀ hAd⟩
  · intro q hq hq1 hq2
    haveI := hq.isPrime
    let Q : HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) :=
      ⟨q, hq.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hq (RingOfIntegers.not_isField _)⟩
    have hu : Q.under (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ≠ ((F u).atT.eV v).1 := fun h =>
      (GlobalTheory.T.host_primes_over_level_place I hOk hP l Z H F hS hC u v Q h).elim hq1 hq2
    have h1 := GlobalTheory.T.adelic_conjugate_character_standard_forms I hOk hP l Z H F hS hC u i hi v c _ γ₀.1 hAd Q hu
    refine Submodule.map_injective_of_injective
      (f := ((crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X i).V →ₗ[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E] (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N i) → (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)).restrictScalars (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)))
      (crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi).injective ?_
    rw [localization_map₂ hi, localization_map₂ hi, lc_gmap]
    exact h1
  · have e : lc ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X i) (rankN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi) (Formalism.L2.Herm.Ld (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u i (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).fm u).dn i v c g)) =
        Formalism.L2.Forms.Ld (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u i hi (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).fm u).dn i v c g) :=
      dual_co (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.cm ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X i) (rankN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).clsLat u i _)
    refine Submodule.map_injective_of_injective
      (f := ((crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X i).V →ₗ[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E] (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N i) → (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)).restrictScalars (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)))
      (crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi).injective ?_
    rw [localization_map₂ hi, localization_map₂ hi, lc_gmap]
    refine Eq.trans ?_ hloc
    exact congrArg (fun L => Formalism.HermitianLatticesTheory.localization₂ ((F u).atT.Pv v) (Formalism.L2.Forms.mulLat γ₀.1.1 L)) e
  · intro z hz
    rw [prH_eq _ _ hi, prkH_eq _ _ hi]
    have hx : γ₀.1.1 *ᵥ (toLd i hi _ z).1 ∈ Formalism.L2.Forms.Lk (F u).atT i hi v c := by
      rw [show (toLd i hi _ z).1 = crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi z.1 from rfl, ← crdN_gx]
      exact (mem_Lk (F u).atT i hi v c _).1 hz
    rw [hfv _ hx]
    exact congrArg g (congrArg _ (Subtype.ext (crdN_gx i hi γ₀ z.1).symm))
  · intro v' hv' z hz
    rw [prH_eq _ _ hi, prH_eq _ _ hi]
    exact GlobalTheory.T.levelFunctional_eq_of_classes_related_at_place I hOk hP l Z H F hS hC u i hi v v' c _ γ₀.1 hAd hv' (toLd i hi c ⟨_, hz⟩) (toLd i hi _ z)
      (crdN_gx i hi γ₀ z.1)

end GlobalTheory.Mem.Col2.HAt


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.Col2.HAt.dn_move_exists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (F : ∀ u, FormsTiedSym (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i v (c : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).mem u).C.cls i) (g : Module.Dual (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).mem u).A.Fv v) (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).fm u).lk i v c)), ∃ γ, i ≤ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m → g ≠ 0 → DnCl (F u).atT (F u).lv i v c g γ ∧ AdOf H u i c (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).fm u).dn i v c g) γ v := by
  intro B X I hOk hP l Z H F hS hC u i v c g
  by_cases hcase : i ≤ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m ∧ g ≠ 0
  · obtain ⟨hi, hg⟩ := hcase
    by_cases hN : i = 0 ∨ i = (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m
    · obtain ⟨γ, η, κ, hη, hy, hloc, hfv, -⟩ := (F u).dnN i hi hN v c g hg
      refine ⟨gx i hi γ, fun _ _ => dnCl_of_tie I hOk hP l Z H F hS hC u i hi v c g γ
        ⟨fun _ => ⟨κ.1, κ.2, η.1, η.2, hη, hy⟩, fun h1 h2 => absurd hN (by omega)⟩ hloc hfv⟩
    · have h1 : 1 ≤ i := by omega
      have h2 : i + 1 ≤ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m := by omega
      obtain ⟨hβ, γ, η, κ, hη, hy, hloc, hfv, -⟩ := (F u).dnC i h1 h2 v (H.chOf u i c) ⟨c, rfl⟩ g hg
      refine ⟨gx i hi γ, fun _ _ => dnCl_of_tie I hOk hP l Z H F hS hC u i hi v c g γ
        ⟨fun h => absurd h hN, fun _ _ => ⟨hβ, κ.1, κ.2, η.1, η.2, hη, hy⟩⟩ hloc ?_⟩
      intro x hx
      rw [← (GlobalTheory.T.middleStep_oneLevel_projection_eq_chart_projection I hOk hP l Z H F hS hC u i h1 h2 v (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).fm u).dn i v c g)).1 x x rfl,
        ← (GlobalTheory.T.middleStep_oneLevel_projection_eq_chart_projection I hOk hP l Z H F hS hC u i h1 h2 v c).2 ⟨_, hx⟩ ⟨_, hx⟩ rfl]
      exact hfv x hx
  · exact ⟨1, fun hi hg => absurd ⟨hi, hg⟩ hcase⟩
