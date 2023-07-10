/*
 * Copyright 2008 the original author or authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.powermock.api.mockito.powermocklistener;

/**
 * Before each test method all fields annotated with {@link Mock},
 * {@link org.mockito.Mock} or {@link Mock} have mock objects created for them
 * and injected to the fields.
 * 
 * @deprecated Test Runners uses an annotation enabling listener per default
 *             since version 1.3. You should just remove this listener.
 */
public class AnnotationEnabler extends org.powermock.api.extension.listener.AnnotationEnabler {

}
