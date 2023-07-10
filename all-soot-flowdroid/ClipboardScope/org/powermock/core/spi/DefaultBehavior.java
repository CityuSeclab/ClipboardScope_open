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

package org.powermock.core.spi;

/**
 * Interface that provides the replay, verify and reset behavior for mock
 * objects and classes.
 */
public interface DefaultBehavior {

	/**
	 * Replay the given objects or classes. May throw exception if replay is not
	 * needed or not supported.
	 * 
	 * @param mock
	 *            The object(s) to replay. May be <code>null</code>.
	 * 
	 * @return the result of the replay (may be <code>null</code>).
	 */
	Object replay(Object... mocks);

	/**
	 * Verify the given objects or classes. May throw exception if verify is not
	 * needed or not supported.
	 * 
	 * @param mock
	 *            The object(s) to verify. May be <code>null</code>.
	 * 
	 * @return the result of the verification (may be <code>null</code>).
	 */
	Object verify(Object... mocks);

	/**
	 * Reset the given objects or classes. May throw exception if reset is not
	 * needed or not supported.
	 * 
	 * @param mock
	 *            The object(s) to replay. May be <code>null</code>.
	 * 
	 * @return the result of the replay (may be <code>null</code>).
	 */
	Object reset(Object... mocks);

}
