/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.WellFoundedSet

/-!
# Results for mathlib

A collection of results for the disproof of the Aharoni–Korman conjecture which should be in
mathlib.
-/

namespace LeanPool.AharoniKorman

lemma chain_intersect_antichain {α : Type*} [PartialOrder α] {s t : Set α}
    (hs : IsChain (· ≤ ·) s) (ht : IsAntichain (· ≤ ·) t) :
    (s ∩ t).Subsingleton := by
  exact inter_subsingleton_of_isChain_of_isAntichain hs ht

end LeanPool.AharoniKorman
