/*
 * Copyright 2011 the original author or authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.powermock.core.classloader.annotations;

import org.powermock.core.spi.PowerMockTestListener;

import java.lang.annotation.*;

/**
 * The PowerMock listener annotation can be used to tell PowerMock which
 * listeners should be instantiated and invoked during a test. A listener is
 * invoked according to the events specified in the
 * {@link PowerMockTestListener} interface.
 */
@Target( { ElementType.TYPE })
@Retention(RetentionPolicy.RUNTIME)
@Documented
@Inherited
public @interface PowerMockListener {
	Class<? extends PowerMockTestListener>[] value();
}
