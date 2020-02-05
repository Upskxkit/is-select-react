/// <reference types="react" />
import PropTypes from "prop-types";
import { WithPopper } from "../interface";
declare const withPopper: {
    ({ children, relative, request }: WithPopper): JSX.Element;
    propTypes: {
        children: PropTypes.Validator<(...args: any[]) => any>;
        relative: PropTypes.Requireable<boolean>;
        request: PropTypes.Requireable<(...args: any[]) => any>;
    };
};
export default withPopper;
