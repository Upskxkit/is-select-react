import * as PropTypes from "prop-types";

export const item = PropTypes.shape({
  value: PropTypes.any,
  label: PropTypes.string,
  id: PropTypes.string,
  checked: PropTypes.bool,
  disabled: PropTypes.bool
});

export const propTypes = (otherProps?: object): object => ({
  open: PropTypes.bool,
  anchorEl: PropTypes.object,
  cancelHandler: PropTypes.func,
  applyHandler: PropTypes.func,
  items: PropTypes.arrayOf(item),
  ...otherProps
});
