// Copyright 2020 The Casbin Authors. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

import { EffectorStream } from './effectorStream';
import { Effect } from './effector';
import { EffectExpress } from '../constants';
import type { Mode, Eft, EffectState } from './effectorPure';
import { pushEffectStep } from './effectorPure';

function toMode(expr: string): Mode {
  switch (expr) {
    case EffectExpress.ALLOW:
      return 'allow';
    case EffectExpress.DENY:
      return 'deny';
    case EffectExpress.ALLOW_AND_DENY:
      return 'allow_and_deny';
    case EffectExpress.PRIORITY:
    case EffectExpress.SUBJECT_PRIORITY:
      return 'priority';
    default:
      throw new Error('unsupported effect');
  }
}

function toEft(eft: Effect): Eft {
  switch (eft) {
    case Effect.Allow:
      return 'allow';
    case Effect.Deny:
      return 'deny';
    default:
      return 'indeterminate';
  }
}

/**
 * DefaultEffectorStream — delegates to the verified pure function pushEffectStep.
 */
export class DefaultEffectorStream implements EffectorStream {
  private state: EffectState = { res: false, recorded: false, done: false };
  private readonly mode: Mode;

  constructor(expr: string) {
    this.mode = toMode(expr);
  }

  current(): boolean {
    return this.state.res;
  }

  public pushEffect(eft: Effect): [boolean, boolean, boolean] {
    this.state = pushEffectStep(this.mode, toEft(eft), this.state);
    return [this.state.res, this.state.recorded, this.state.done];
  }
}
